const std = @import("std");

const assert = std.debug.assert;
const testing = std.testing;

const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayListUnmanaged;

const SearchResult = union(enum) {
    /// The exact key was found at the given index.
    found: usize,
    /// The key was not found. The returned index was that of the child node that may contain the key.
    not_found: usize,
};

inline fn splitArrayListAssumeCapacity(comptime T: type, one: *ArrayList(T), two: *ArrayList(T), idx: usize) void {
    two.appendSliceAssumeCapacity(one.items[idx..]);
    one.shrinkRetainingCapacity(idx);
}

/// This a BTree that guarantees the following invariants:
///     - number of keys in each node is within the range [degree - 1, 2 * degree - 1] except for
///       root nodes which may contain [0, 2 * degree -1] keys
///     - number of children in each non-leaf node is `number of keys + 1`
///     - all keys in a node are in sorted order
///
/// This follows an API similar to std.HashMap.
///
/// Initilization should be done in the following manner:
///
/// ```
/// const BTree = Btree(usize, usize, compareUsizeFn);
///
/// var btree: BTree = undefined;
/// btree.init(3, allocator);
/// defer btree.deinit();
/// ```
///
pub fn Btree(comptime KeyT: type, ValueT: type, comptime compare_fn: (fn (a: KeyT, b: KeyT) std.math.Order)) type {
    return struct {
        const Self = @This();

        const KeyArray = std.ArrayListUnmanaged(KeyT);
        const ValueArray = std.ArrayListUnmanaged(ValueT);
        const ChildrenArray = std.ArrayListUnmanaged(Node);
        const SearchStack = std.ArrayListUnmanaged(SearchStackElement);
        const SplitResult = struct { key: KeyT, value: ValueT, new_node: Node };
        const SearchStackElement = struct {
            node: *Node,
            idx: usize,
        };

        pub const KeyValuePair = struct { key: KeyT, value: ValueT };
        pub const KeyValuePairPtr = struct { key: *KeyT, value: *ValueT };

        const Node = struct {
            keys: KeyArray,
            values: ValueArray,
            // Only for internal nodes.
            // TODO: Consider making this ?ChildrenArray.
            children: ChildrenArray,

            fn initLeafNode(self: *Node, keys_max: usize, allocator: Allocator) !void {
                // TODO: multi-item pointer (allows for pointer arithmetic). See if switching to this
                // and then storing only one `len: usize` and three pointers (to the keys, values and children)
                // is more performant, and if so, by how much. This is essentially what is being done in the
                // Rust version. If this is more performant, the question to answer would be whether the speed
                // up is worth the complexity. Regardless, I want to implement such a version because it would
                // be fun and a nice opportunity to understand how to deal with multi-item pointers in Zig.
                self.* = .{
                    .keys = try KeyArray.initCapacity(allocator, keys_max),
                    .values = try ValueArray.initCapacity(allocator, keys_max),
                    .children = ChildrenArray.initBuffer(&[_]Node{}),
                };
            }

            fn initInternalNode(self: *Node, keys_max: usize, allocator: Allocator) !void {
                self.* = .{
                    .keys = try KeyArray.initCapacity(allocator, keys_max),
                    .values = try ValueArray.initCapacity(allocator, keys_max),
                    .children = try ChildrenArray.initCapacity(allocator, keys_max + 1),
                };
            }

            /// Find either the index that holds the key or the index of the child
            /// subtree that must contain the key, if it exists.
            fn search(self: *const Node, key: KeyT) SearchResult {
                for (self.keys.items, 0..) |k, idx| {
                    switch (compare_fn(k, key)) {
                        .eq => return .{ .found = idx },
                        // idx = left child of the first key that's greater than `key`
                        .gt => return .{ .not_found = idx },
                        .lt => {},
                    }
                }

                // Implies that all the keys in this node are smaller than the key we're searching
                // for. In this case, we have to search the rightmost subtree if this is an internal node.
                return .{ .not_found = self.len() };
            }

            /// Insert into the node as if it was a leaf node.
            fn insertLeaf(self: *Node, key: KeyT, value: ValueT, idx: usize, allocator: Allocator) !?SplitResult {
                if (self.isFull()) {
                    var split_result = try self.splitLeaf(allocator);

                    // If the index we're supposed to insert in case of no splitting was
                    // less than or equal to the pivot index, then we insert it into the
                    // left node (i.e. this node) else we insert it into the right node.
                    //
                    // NOTE: pivot index = length of the left node
                    const left_node_len = self.len();
                    if (idx <= left_node_len) {
                        self.insertLeafAssumeCapacity(key, value, idx);
                    } else {
                        // right_node_idx = (idx - (left_node_len + 1))
                        split_result.new_node.insertLeafAssumeCapacity(key, value, idx - left_node_len - 1);
                    }

                    return split_result;
                }

                self.insertLeafAssumeCapacity(key, value, idx);

                return null;
            }

            /// Insert into the node as if it was an internal node.
            fn insertInternal(self: *Node, key: KeyT, value: ValueT, right_child: Node, idx: usize, allocator: Allocator) !?SplitResult {
                if (self.isFull()) {
                    var split_result = try self.splitInternal(allocator);

                    const left_node_len = self.len();
                    if (idx <= left_node_len) {
                        self.insertInternalAssumeCapacity(key, value, right_child, idx);
                    } else {
                        split_result.new_node.insertInternalAssumeCapacity(key, value, right_child, idx - left_node_len - 1);
                    }

                    return split_result;
                }

                self.insertInternalAssumeCapacity(key, value, right_child, idx);

                return null;
            }

            /// Remove the value from the node at the given index.
            ///
            /// This must be called only on a leaf node.
            inline fn removeLeaf(self: *Node, idx: usize) void {
                assert(self.isLeaf());

                _ = self.keys.orderedRemove(idx);
                _ = self.values.orderedRemove(idx);
            }

            /// Handle the underflowing of the child at the given index by either
            /// stealing from one of it's siblings or merging with one of it's
            /// siblings.
            ///
            /// This takes an allocator, but not for allocating memory for deallocating
            /// a node in case of a merge.
            fn handleUnderflowOfChild(self: *Node, underflowed_child_idx: usize, allocator: Allocator) void {
                if (underflowed_child_idx == 0) {
                    const right_child = &self.children.items[underflowed_child_idx + 1];
                    if (right_child.hasEnoughToSteal()) {
                        self.stealFromRight(underflowed_child_idx);
                    } else {
                        self.mergeChildren(underflowed_child_idx, allocator);
                    }
                } else {
                    const left_child = &self.children.items[underflowed_child_idx - 1];
                    if (left_child.hasEnoughToSteal()) {
                        self.stealFromLeft(underflowed_child_idx);
                    } else {
                        self.mergeChildren(underflowed_child_idx - 1, allocator);
                    }
                }
            }

            /// Merge the left and right children into one node.
            fn mergeChildren(self: *Node, left_child_idx: usize, allocator: Allocator) void {
                const key = self.keys.orderedRemove(left_child_idx);
                const value = self.values.orderedRemove(left_child_idx);
                var right_child = self.children.orderedRemove(left_child_idx + 1);
                defer right_child.deinit(allocator);

                // Move the key from the parent into the left child.
                var left_child = &self.children.items[left_child_idx];
                left_child.keys.appendAssumeCapacity(key);
                left_child.values.appendAssumeCapacity(value);

                // Move everything from the right child into the left child.
                left_child.keys.appendSliceAssumeCapacity(right_child.keys.items);
                left_child.values.appendSliceAssumeCapacity(right_child.values.items);

                if (left_child.isLeaf() == false) {
                    assert(right_child.isLeaf() == false);

                    left_child.children.appendSliceAssumeCapacity(right_child.children.items);
                }
            }

            /// Move the biggest key in the left child, and the key in this node in the right direction one time.
            fn stealFromLeft(self: *Node, underflowed_child_idx: usize) void {
                const left_child_idx = underflowed_child_idx - 1;

                var left_child = &self.children.items[left_child_idx];
                var key = left_child.keys.pop();
                var value = left_child.values.pop();

                // Move the parent's key and value into `key` and `value`.
                std.mem.swap(KeyT, &key, &self.keys.items[left_child_idx]);
                std.mem.swap(ValueT, &value, &self.values.items[left_child_idx]);

                var right_node = &self.children.items[underflowed_child_idx];
                right_node.insertLeafAssumeCapacity(key, value, 0);

                if (left_child.isLeaf() == false) {
                    assert(right_node.isLeaf() == false);

                    const child_to_steal = left_child.children.pop();
                    right_node.children.insertAssumeCapacity(0, child_to_steal);
                }
            }

            /// Move the smallest key in the right child, the key in this node in the left direction one time.
            fn stealFromRight(self: *Node, underflowed_child_idx: usize) void {
                var right_child = &self.children.items[underflowed_child_idx + 1];
                var key = right_child.keys.orderedRemove(0);
                var value = right_child.values.orderedRemove(0);

                std.mem.swap(KeyT, &key, &self.keys.items[underflowed_child_idx]);
                std.mem.swap(ValueT, &value, &self.values.items[underflowed_child_idx]);

                var left_child = &self.children.items[underflowed_child_idx];
                left_child.keys.appendAssumeCapacity(key);
                left_child.values.appendAssumeCapacity(value);

                // Steal the child as well.
                if (right_child.isLeaf() == false) {
                    assert(left_child.isLeaf() == false);

                    const child_to_steal = right_child.children.orderedRemove(0);
                    left_child.children.appendAssumeCapacity(child_to_steal);
                }
            }

            inline fn insertLeafAssumeCapacity(self: *Node, key: KeyT, value: ValueT, idx: usize) void {
                self.keys.insertAssumeCapacity(idx, key);
                self.values.insertAssumeCapacity(idx, value);
            }

            inline fn insertInternalAssumeCapacity(self: *Node, key: KeyT, value: ValueT, right_child: Node, idx: usize) void {
                self.keys.insertAssumeCapacity(idx, key);
                self.values.insertAssumeCapacity(idx, value);
                self.children.insertAssumeCapacity(idx + 1, right_child);
            }

            /// Split the node into two.
            ///
            /// This keeps elements in the range `[0..degree - 2]` in this node and `[degree..]` in
            /// new node. The element at `degree - 1` acts as the pivot.
            inline fn splitLeaf(self: *Node, allocator: Allocator) !SplitResult {
                // Add 1 to ensure we keep the pivot key/value in the left node.
                const pivot_idx = self.len() / 2 + 1;
                var new_node: Node = undefined;
                try new_node.initLeafNode(self.keys.items.len, allocator);

                splitArrayListAssumeCapacity(KeyT, &self.keys, &new_node.keys, pivot_idx);
                splitArrayListAssumeCapacity(ValueT, &self.values, &new_node.values, pivot_idx);

                return .{ .key = self.keys.pop(), .value = self.values.pop(), .new_node = new_node };
            }

            /// Same as `splitLeaf` except the children are split as well.
            inline fn splitInternal(self: *Node, allocator: Allocator) !SplitResult {
                const pivot_idx = self.len() / 2 + 1;
                var new_node: Node = undefined;
                try new_node.initInternalNode(self.keys.items.len, allocator);

                splitArrayListAssumeCapacity(KeyT, &self.keys, &new_node.keys, pivot_idx);
                splitArrayListAssumeCapacity(ValueT, &self.values, &new_node.values, pivot_idx);
                splitArrayListAssumeCapacity(Node, &self.children, &new_node.children, pivot_idx);

                return .{ .key = self.keys.pop(), .value = self.values.pop(), .new_node = new_node };
            }

            /// Get the number of keys in this node.
            inline fn len(self: *const Node) usize {
                return self.keys.items.len;
            }

            /// Get the maximum number of keys this node can hold.
            inline fn capacity(self: *const Node) usize {
                return self.keys.capacity;
            }

            inline fn isFull(self: *const Node) bool {
                return self.len() >= self.capacity();
            }

            inline fn isUnderflow(self: *const Node) bool {
                return self.len() < self.capacity() / 2;
            }

            /// Check whether this node has enough elements for us to steal one
            /// without it resulting in an underflow.
            inline fn hasEnoughToSteal(self: *const Node) bool {
                return self.len() > self.capacity() / 2;
            }

            inline fn isLeaf(self: *const Node) bool {
                return self.children.items.len == 0;
            }

            /// Free the memory used by this node and all it's children.
            fn deinitAlongWithChildren(self: *Node, allocator: Allocator) void {
                for (self.children.items) |*child| {
                    child.deinitAlongWithChildren(allocator);
                }

                self.deinit(allocator);
            }

            /// This frees only the resources used by this node without including
            /// all the memory used by it's children.
            fn deinit(self: *Node, allocator: Allocator) void {
                self.keys.deinit(allocator);
                self.values.deinit(allocator);
                if (self.isLeaf() == false) {
                    self.children.deinit(allocator);
                }
            }

            fn print(self: *const Node, indent: usize, child_num: usize, is_root: bool) void {
                if (is_root) {
                    std.debug.print("Root: {any}\n", .{self.keys.items});
                } else {
                    for (0..indent * 2) |_| {
                        std.debug.print(" ", .{});
                    }
                    std.debug.print("Child {}: {any}\n", .{ child_num, self.keys.items });
                }
                for (self.children.items, 0..) |*child, i| {
                    child.print(indent + 1, i, false);
                }
            }
        };

        /// A read-only field that gives the number of elements in the btree.
        len: usize = 0,

        /// A read-only field that describes the degree of the btree.
        degree: u16,

        /// A read-only field that gives the depth of the btree.
        depth: usize = 1,

        /// Don't touch this. Unless you know what you're doing. Then go nuts.
        root: Node = undefined,

        /// The allocator used for any allocations/deallocations during the lifetime
        /// of this btree.
        allocator: std.mem.Allocator,

        pub fn init(self: *Self, degree: u16, allocator: Allocator) !void {
            self.* = .{
                .degree = degree,
                .allocator = allocator,
            };
            try self.root.initLeafNode(2 * degree - 1, allocator);
        }

        /// Add the given key-value pair to the btree.
        ///
        /// This will overwrite any existing values.
        pub fn put(self: *Self, key: KeyT, value: ValueT) !void {
            // We traverse the tree from the root node onwards to see if the key exists.
            // If the key exists, then we simply overwrite the value.
            // If the key does not exist, then we keep going until we find a leaf node:
            //    - leaf node is full => split the node into two and propagate the split upwards
            //    - leaf node is not full => add the key in the correct location
            //        - the correct location is the index that is returned by `Node.search`
            //
            // If a node is split, then we find it's parent node (which we keep track of using a stack)
            // then try to insert into it. If that node is full, then split and propagate else we're done.
            // The only special case is if we split the root node. Then we have to create a new root node
            // and set the pivot as the only element within the root node.

            const depth = self.depth;
            var i: usize = 0;
            var stack = try SearchStack.initCapacity(self.allocator, depth);
            defer stack.deinit(self.allocator);

            var curr_node = &self.root;
            const idx = search: {
                while (i < depth) : (i += 1) {
                    switch (curr_node.search(key)) {
                        .found => |idx| {
                            curr_node.values.items[idx] = value;

                            return;
                        },
                        .not_found => |idx| {
                            if (curr_node.isLeaf()) {
                                break :search idx;
                            }

                            stack.appendAssumeCapacity(.{ .node = curr_node, .idx = idx });
                            curr_node = &curr_node.children.items[idx];
                        },
                    }
                }
                unreachable;
            };

            self.len += 1;

            assert(curr_node.isLeaf());

            var split = try curr_node.insertLeaf(key, value, idx, self.allocator) orelse return;

            // Propagate the split towards the root.
            while (stack.popOrNull()) |*node_path| {
                split = try node_path.node.insertInternal(split.key, split.value, split.new_node, node_path.idx, self.allocator) orelse return;
            }

            // If we reached here, then that means the root itself was split.
            var new_root: Node = undefined;
            try new_root.initInternalNode(2 * self.degree - 1, self.allocator);
            new_root.keys.appendAssumeCapacity(split.key);
            new_root.values.appendAssumeCapacity(split.value);
            new_root.children.appendAssumeCapacity(self.root);
            new_root.children.appendAssumeCapacity(split.new_node);

            self.root = new_root;
            self.depth += 1;
        }

        /// Get the value associated with the given key.
        pub fn get(self: *Self, key: KeyT) ?ValueT {
            // Traverse the tree from the root node onwards. In each node see if the key exists,
            // and if we found it then we can stop traversing. If the key wasn't found, then we have two cases:
            //    - node we're searching is a leaf node in which case the key doesn't exist
            //    - node we're searching is an internal node in which case we search the subtree

            var i: usize = 0;
            var curr_node: *const Node = &self.root;
            const depth = self.depth;

            while (i < depth) : (i += 1) {
                const idx = blk: {
                    switch (curr_node.search(key)) {
                        .found => |idx| return curr_node.values.items[idx],
                        .not_found => |idx| {
                            // If we get to a leaf node and we don't find it, then the key simply doesn't exist.
                            if (curr_node.isLeaf()) {
                                return null;
                            }

                            break :blk idx;
                        },
                    }
                };

                curr_node = &curr_node.children.items[idx];
            }

            // We either reach find the key in some node or reach a leaf node that also doesn't
            // have the key at which point we should have already returned null. So we should never
            // reach here. If we did, then we traversed more than the depth of the tree which is a bug.
            // `maximum number of nodes traversed = depth of btree`
            unreachable;
        }

        /// Get the key-value pair for the smallest key in the btree.
        ///
        /// Returns null if the btree is empty.
        pub fn getSmallest(self: *const Self) ?KeyValuePair {
            if (self.len == 0) {
                return null;
            }

            const leftmost_child = self.getLefmostChild();

            return .{ .key = leftmost_child.keys.items[0], .value = leftmost_child.values.items[0] };
        }

        /// Get the key-value pair for the smallest key in the btree.
        ///
        /// This returns the pointers to the key and the value. While you can modify them,
        /// if you modify the key in such a way that it affects the sorting then things will break.
        /// Also, the pointers are invalidated on any call that may insert or remove values
        /// from the btree.
        pub fn getSmallestPtr(self: *const Self) ?KeyValuePairPtr {
            if (self.len == 0) {
                return null;
            }

            const leftmost_child = self.getLefmostChild();

            return .{ .key = &leftmost_child.keys.items[0], .value = &leftmost_child.values.items[0] };
        }

        fn getLefmostChild(self: *const Self) *const Node {
            assert(self.len > 0);
            var curr_node: *const Node = &self.root;
            while (curr_node.isLeaf() == false) {
                curr_node = &curr_node.children.items[0];
            }

            return curr_node;
        }

        /// Get the key-value pair for the largest key in the btree.
        ///
        /// Returns null if the btree is empty.
        pub fn getLargest(self: *const Self) ?KeyValuePair {
            if (self.len == 0) {
                return null;
            }

            const rightmost_child = self.getRightmostChild();

            return .{ .key = rightmost_child.keys.getLast(), .value = rightmost_child.values.getLast() };
        }

        /// Get the key-value pair for the largest key in the btree.
        ///
        /// This returns the pointers to the key and the value. While you can modify them,
        /// if you modify the key in such a way that it affects the sorting then things will break.
        /// Also, the pointers are invalidated on any call that may insert or remove values
        /// from the btree.
        pub fn getLargestPtr(self: *const Self) ?KeyValuePairPtr {
            if (self.len == 0) {
                return null;
            }

            const rightmost_child = self.getRightmostChild();
            const rightmost_child_len = rightmost_child.len();

            return .{ .key = &rightmost_child.keys.items[rightmost_child_len - 1], .value = &rightmost_child.values.items[rightmost_child_len - 1] };
        }

        fn getRightmostChild(self: *const Self) *const Node {
            assert(self.len > 0);

            var curr_node: *const Node = &self.root;
            while (curr_node.isLeaf() == false) {
                curr_node = &curr_node.children.getLast();
            }
            return curr_node;
        }

        /// Remove the key from the btree.
        ///
        /// If the key doesn't exist, this is a no-op.
        pub fn remove(self: *Self, key: KeyT) !bool {
            // We first find the key within the btree.
            // If it doesn't exist, then we don't need to do anything. The simplest case.
            //
            // The logic for removing the key differs based on the node type:
            //
            //     - If the node is a leaf node, then we simply remove the key and it's value
            //
            //     - If the node is an internal node, then we swap that element with the smallest key
            //       in it's right subtree. This element will always be at a leaf node. Then we remove
            //       from that leaf node that contained the smallest key. By doing this swapping, we ensure
            //       that we maintain the invariant of a btree that all the elements in the right child
            //       of a key must be greater than or equal to the key.
            //
            // Removing results in an underflow, but we can steal without undeflowing (assume we're stealing from the left sibling):
            //
            //     - We take the key from the "left" parent of the node that underflowed, and set that as the first key.
            //       The largest key in the left sibling takes the place of the key that the underflowed node took in the
            //       left parent. We can't just take directly from the left sibling because that would break the invariant
            //       of all the keys in the right subtree of a node must have a value greater than or equal to the key (this
            //       invariant would be broken for the "left" parent of the underflowed node).
            //
            //     - The rightmost child of the key that was taken now becomes the leftmost child of the first key
            //       in the undeflowed node. Once again, this allows the maintaining of the invariants.
            //
            // Removing results in an underflow, and stealing also results in an underflow (assume we tried to steal from the left sibling):
            //
            //     - We have to merge the underflowed node with it's left sibling. We insert the common parent key into it's left child, and then
            //       we move all the keys in the underflowed node into the left sibling. Then we remove the parent key from the common parent node.
            //
            //     - The merged node will always have `2 * degree - 2` keys which means that we never have to deal
            //       splitting etc.
            //
            //     - Removing the key from the parent may result in it underflowing, in which case we have to follow the logic of
            //       removing a key again.
            //

            const depth = self.depth;
            var i: usize = 0;
            var stack = try SearchStack.initCapacity(self.allocator, depth);
            defer stack.deinit(self.allocator);

            var curr_node = &self.root;
            var idx = search: {
                while (i < depth) : (i += 1) {
                    switch (curr_node.search(key)) {
                        .found => |idx| {
                            break :search idx;
                        },
                        .not_found => |idx| {
                            if (curr_node.isLeaf()) {
                                return false;
                            }

                            stack.appendAssumeCapacity(.{ .node = curr_node, .idx = idx });
                            curr_node = &curr_node.children.items[idx];
                        },
                    }
                }
                unreachable;
            };

            if (curr_node.isLeaf() == false) {
                var internal_node = curr_node;
                // If it's an internal node, then we have to find the smallest key-value pair and swap it.
                // To do this, we first go to it's right child, and then we keep going left until we hit a leaf node.
                curr_node = &curr_node.children.items[idx + 1];

                while (curr_node.isLeaf() == false) {
                    stack.appendAssumeCapacity(.{ .node = curr_node, .idx = 0 });
                    curr_node = &curr_node.children.items[0];
                }

                std.mem.swap(KeyT, &internal_node.keys.items[idx], &curr_node.keys.items[0]);
                std.mem.swap(ValueT, &internal_node.values.items[idx], &curr_node.values.items[0]);
                idx = 0;
            }

            curr_node.removeLeaf(idx);

            while (curr_node.isUnderflow()) {
                if (stack.popOrNull()) |node_path| {
                    node_path.node.handleUnderflowOfChild(node_path.idx, self.allocator);
                    curr_node = node_path.node;
                } else {
                    // We took an element from the root node. If the root node is an internal node,
                    // then we make it's only child into the new root. If it's a leaf node, we just
                    // leave it alone since this may happen when all the elements from the btree are
                    // deleted.
                    if (self.root.len() == 0 and self.root.isLeaf() == false) {
                        assert(self.root.children.items.len == 1);
                        var old_root = self.root;
                        defer old_root.deinit(self.allocator);

                        self.root = self.root.children.pop();
                    }

                    break;
                }
            }

            self.len -= 1;

            return true;
        }

        pub fn deinit(self: *Self) void {
            self.root.deinitAlongWithChildren(self.allocator);
        }

        /// Pretty print the btree.
        pub fn print(self: *const Self) void {
            self.root.print(0, 0, true);
        }
    };
}

/// This is the same as `testing.expectEqual` except that it takes in the `actual` value first.
/// This helps with the correct type resolution.
/// REFERENCE: https://github.com/ziglang/zig/issues/4437
fn expectEqual(actual: anytype, expected: anytype) !void {
    try testing.expectEqual(expected, actual);
}

fn compareUsize(a: usize, b: usize) std.math.Order {
    return std.math.order(a, b);
}

const less_than_fn = std.sort.asc(usize);

/// Check that the btree is valid by ensuring all the invariants
/// regarding a btree is maintained.
fn validateBtree(btree: *const BtreeType) !void {
    if (btree.len == 0) {
        try expectEqual(btree.root.keys.items.len, 0);
        try expectEqual(btree.root.values.items.len, 0);
        try expectEqual(btree.root.isLeaf(), true);

        return;
    }

    try testing.expect(btree.root.keys.items.len >= 1);
    try testing.expect(btree.root.keys.items.len < 2 * btree.degree);
    try testing.expect(std.sort.isSorted(usize, btree.root.keys.items, {}, less_than_fn));
    try expectEqual(btree.root.values.items.len, btree.root.keys.items.len);

    if (btree.root.isLeaf() == false) {
        try testing.expectEqual(btree.root.children.items.len, btree.root.keys.items.len + 1);

        for (btree.root.children.items, 0..) |*node, i| {
            try validateNode(node, btree.degree);

            if (i == btree.root.keys.items.len) {
                const key = btree.root.keys.items[i - 1];
                for (node.keys.items) |k| {
                    try testing.expect(k >= key);
                }
            } else {
                const key = btree.root.keys.items[i];
                for (node.keys.items) |k| {
                    try testing.expect(k < key);
                }
            }
        }
    }
}

/// Validate that this node and all it's children follow the invariants.
/// This assumes the node is not a root node since that's a special case.
fn validateNode(node: *const BtreeType.Node, degree: u16) !void {
    const keys_min = degree - 1;
    const keys_max = 2 * degree;

    try testing.expect(node.keys.items.len >= keys_min);
    try testing.expect(node.keys.items.len < keys_max);
    try expectEqual(node.values.items.len, node.keys.items.len);
    try testing.expect(std.sort.isSorted(usize, node.keys.items, {}, less_than_fn));

    if (node.isLeaf() == false) {
        try testing.expectEqual(node.children.items.len, node.keys.items.len + 1);

        for (node.children.items, 0..) |*child, i| {
            try validateNode(child, degree);

            if (i == node.keys.items.len) {
                const key = node.keys.items[i - 1];
                for (child.keys.items) |k| {
                    try testing.expect(k >= key);
                }
            } else {
                const key = node.keys.items[i];
                for (child.keys.items) |k| {
                    try testing.expect(k < key);
                }
            }
        }
    }
}

const BtreeType = Btree(usize, usize, compareUsize);

test "btree: don't split root node" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    for (1..4) |i| {
        try btree.put(i, i);
        try expectEqual(btree.len, i);
        try expectEqual(btree.get(i), i);
    }

    for (1..4) |i| {
        try expectEqual(btree.get(i), i);
    }

    try expectEqual(btree.depth, 1);
    try validateBtree(&btree);
}

test "btree: split root node once into internal node" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    for (1..5) |i| {
        try btree.put(i, i);
        try expectEqual(btree.len, i);
        try expectEqual(btree.get(i), i);
    }

    try expectEqual(btree.depth, 2);
    try validateBtree(&btree);
}

test "btree: split root node twice" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    for (1..11) |i| {
        try btree.put(i, i);
        try expectEqual(btree.len, i);
        try expectEqual(btree.get(i), i);
    }

    try expectEqual(btree.depth, 3);
    try validateBtree(&btree);
}

test "btree: put and get sequential 100" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    for (0..100) |i| {
        try btree.put(i, i);
        try expectEqual(btree.len, i + 1);
    }
    try expectEqual(btree.len, 100);

    for (0..100) |i| {
        try expectEqual(btree.get(i), i);
    }

    try validateBtree(&btree);
}

test "btree: put and get random 100" {
    var prng = std.Random.DefaultPrng.init(10);
    var random = prng.random();

    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    var map = std.AutoHashMap(usize, usize).init(testing.allocator);
    defer map.deinit();

    for (0..100) |_| {
        const key = random.int(usize);
        const value = random.int(usize);

        try btree.put(key, value);
        try map.put(key, value);
    }
    try expectEqual(btree.len, map.count());

    var iterator = map.iterator();
    while (iterator.next()) |*kvp| {
        try expectEqual(btree.get(kvp.key_ptr.*), kvp.value_ptr.*);
    }

    try validateBtree(&btree);
}

test "btree: put and get sequential 100 with degree 10" {
    var btree: BtreeType = undefined;
    try btree.init(10, testing.allocator);
    defer btree.deinit();

    for (0..100) |i| {
        try btree.put(i, i);
        try expectEqual(btree.len, i + 1);
    }
    try expectEqual(btree.len, 100);

    for (0..100) |i| {
        try expectEqual(btree.get(i), i);
    }

    try validateBtree(&btree);
}

test "btree: put and get random 100 with degree 10" {
    var prng = std.Random.DefaultPrng.init(10);
    var random = prng.random();

    var btree: BtreeType = undefined;
    try btree.init(10, testing.allocator);
    defer btree.deinit();

    var map = std.AutoHashMap(usize, usize).init(testing.allocator);
    defer map.deinit();

    for (0..100) |_| {
        const key = random.int(usize);
        const value = random.int(usize);

        try btree.put(key, value);
        try map.put(key, value);
    }
    try expectEqual(btree.len, map.count());

    var iterator = map.iterator();
    while (iterator.next()) |*kvp| {
        try expectEqual(btree.get(kvp.key_ptr.*), kvp.value_ptr.*);
    }

    try validateBtree(&btree);
}

test "btree: put and get random with 10000 with degree 50" {
    var prng = std.Random.DefaultPrng.init(10);
    var random = prng.random();

    var btree: BtreeType = undefined;
    try btree.init(50, testing.allocator);
    defer btree.deinit();

    var map = std.AutoHashMap(usize, usize).init(testing.allocator);
    defer map.deinit();

    for (0..10_000) |_| {
        const key = random.int(usize);
        const value = random.int(usize);

        try btree.put(key, value);
        try map.put(key, value);
    }
    try expectEqual(btree.len, map.count());

    var iterator = map.iterator();
    while (iterator.next()) |*kvp| {
        try expectEqual(btree.get(kvp.key_ptr.*), kvp.value_ptr.*);
    }

    try validateBtree(&btree);
}

test "btree(remove): remove from leaf node without underflow" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    for (1..8) |i| {
        try btree.put(i, i);
    }

    // 6 should be in the rightmost leaf node
    const removed = try btree.remove(6);

    try testing.expect(removed);
    try expectEqual(btree.get(6), null);
    try expectEqual(btree.len, 6);
    try validateBtree(&btree);
}

test "btree(remove): remove from internal node without underflow" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    for (1..14) |i| {
        try btree.put(i, i);
    }

    // 10 should be in the rightmost child of the root node.
    // This should cause the actual removal to be in the leftmost node which should be full (i.e. no underflow).
    const removed = try btree.remove(10);

    try testing.expect(removed);
    try expectEqual(btree.get(10), null);
    try expectEqual(btree.len, 12);
    try validateBtree(&btree);
}

test "btree(remove): remove with underflow resulting in stealing from left sibling (leaf node)" {
    // 1, 5, 6, 2, 3
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    // This should result in a btree with the root node having 5. The left child
    // will have 1, 2, 3 and the right child will have 6.
    try btree.put(1, 1);
    try btree.put(5, 5);
    try btree.put(6, 6);
    try btree.put(2, 2);
    try btree.put(3, 3);

    // This should result in stealing the '3' from the left child.
    const removed = try btree.remove(6);

    try testing.expect(removed);
    try expectEqual(btree.get(6), null);
    try expectEqual(btree.len, 4);
    try expectEqual(btree.get(1), 1);
    try expectEqual(btree.get(2), 2);
    try expectEqual(btree.get(3), 3);
    try expectEqual(btree.get(5), 5);
    try validateBtree(&btree);
}

test "btree(remove): remove with underlfow resulting in stealing from right sibling (leaf node)" {
    // 1, 5, 7, 6

    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    // This should result in a btree with the root node having 5. The left child
    // will have 1 while the right child will have 6, 7.
    try btree.put(1, 1);
    try btree.put(5, 5);
    try btree.put(6, 6);
    try btree.put(7, 7);

    // This should result in stealing the '6' from the right child.
    const removed = try btree.remove(1);

    try testing.expect(removed);
    try expectEqual(btree.get(1), null);
    try expectEqual(btree.len, 3);
    try expectEqual(btree.get(5), 5);
    try expectEqual(btree.get(6), 6);
    try expectEqual(btree.get(7), 7);
    try validateBtree(&btree);
}

test "btree(remove): underflow of right child leads to merging" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    // This should result in the two leftmost children of the root node having
    // one key each: 1 and 10. Thus, removing 10 should result in merging.
    try btree.put(1, 1);
    try btree.put(5, 5);
    try btree.put(10, 10);
    try btree.put(11, 11);
    try btree.put(12, 12);
    try btree.put(13, 13);

    const removed = try btree.remove(10);

    try testing.expect(removed);
    try expectEqual(btree.get(10), null);
    try expectEqual(btree.get(1), 1);
    try expectEqual(btree.get(5), 5);
    try expectEqual(btree.get(11), 11);
    try expectEqual(btree.get(12), 12);
    try expectEqual(btree.get(13), 13);
    try validateBtree(&btree);
}

test "btree(remove): underflow of left child leads to merging" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    // This should result in the two leftmost children of the root node having
    // one key each: 1 and 10. Thus, removing 10 should result in merging.
    try btree.put(1, 1);
    try btree.put(5, 5);
    try btree.put(10, 10);
    try btree.put(11, 11);
    try btree.put(12, 12);
    try btree.put(13, 13);

    const removed = try btree.remove(1);

    try testing.expect(removed);
    try expectEqual(btree.get(1), null);
    try expectEqual(btree.get(5), 5);
    try expectEqual(btree.get(10), 10);
    try expectEqual(btree.get(11), 11);
    try expectEqual(btree.get(12), 12);
    try expectEqual(btree.get(13), 13);
    try validateBtree(&btree);
}

test "btree(remove): sequential removes" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    for (0..1000) |i| {
        try btree.put(i, i);
    }

    for (0..1000) |i| {
        const removed = try btree.remove(i);

        try testing.expect(removed);
        try validateBtree(&btree);
    }

    try expectEqual(btree.len, 0);
}

test "btree(remove): sequential removes in reverse order" {
    var btree: BtreeType = undefined;
    try btree.init(2, testing.allocator);
    defer btree.deinit();

    for (0..1000) |i| {
        try btree.put(i, i);
    }

    var i: usize = 1000;
    while (i > 0) {
        i -= 1;
        const removed = try btree.remove(i);

        try testing.expect(removed);
        try validateBtree(&btree);
    }

    try expectEqual(btree.len, 0);
}

test "btree(crud): 10000 random elements with degree 4" {
    var prng = std.Random.DefaultPrng.init(10);
    var random = prng.random();

    var btree: BtreeType = undefined;
    try btree.init(4, testing.allocator);
    defer btree.deinit();

    var map = std.hash_map.AutoHashMap(usize, usize).init(testing.allocator);
    defer map.deinit();

    for (0..10000) |_| {
        const key = random.int(usize);

        // Put, get, or delete
        switch (random.intRangeLessThan(u8, 0, 3)) {
            0 => {
                const value = random.int(usize);
                try btree.put(key, value);
                try map.put(key, value);
            },
            1 => {
                try expectEqual(btree.get(key), map.get(key));
            },
            2 => {
                const map_removed = map.remove(key);
                const btree_removed = try btree.remove(key);

                try expectEqual(btree_removed, map_removed);
            },
            else => unreachable,
        }

        try validateBtree(&btree);
    }

    try expectEqual(btree.len, map.count());
    try validateBtree(&btree);
}

test "btree(crud): 10000 random elements with degree 20" {
    var prng = std.Random.DefaultPrng.init(10);
    var random = prng.random();

    var btree: BtreeType = undefined;
    try btree.init(20, testing.allocator);
    defer btree.deinit();

    var map = std.hash_map.AutoHashMap(usize, usize).init(testing.allocator);
    defer map.deinit();

    for (0..10000) |_| {
        const key = random.int(usize);

        // Put, get, or delete
        switch (random.intRangeLessThan(u8, 0, 3)) {
            0 => {
                const value = random.int(usize);
                try btree.put(key, value);
                try map.put(key, value);
            },
            1 => {
                try expectEqual(btree.get(key), map.get(key));
            },
            2 => {
                const map_removed = map.remove(key);
                const btree_removed = try btree.remove(key);

                try expectEqual(btree_removed, map_removed);
            },
            else => unreachable,
        }

        try validateBtree(&btree);
    }

    try expectEqual(btree.len, map.count());
    try validateBtree(&btree);
}

test "btree: getSmallest" {
    var prng = std.Random.DefaultPrng.init(10);
    var random = prng.random();

    var btree: BtreeType = undefined;
    try btree.init(4, testing.allocator);
    defer btree.deinit();

    var keys: [100]usize = undefined;
    for (0..keys.len) |i| {
        keys[i] = random.intRangeAtMost(usize, 1, std.math.maxInt(usize));
    }

    for (keys) |key| {
        try btree.put(key, key - 1);
    }
    std.sort.block(usize, &keys, {}, std.sort.asc(usize));

    const kvp_smallest = btree.getSmallest();
    try expectEqual(kvp_smallest, BtreeType.KeyValuePair{ .key = keys[0], .value = keys[0] - 1 });
}

test "btree: getSmallestPtr" {
    var prng = std.Random.DefaultPrng.init(10);
    var random = prng.random();

    var btree: BtreeType = undefined;
    try btree.init(4, testing.allocator);
    defer btree.deinit();

    var keys: [100]usize = undefined;
    for (0..keys.len) |i| {
        keys[i] = random.intRangeAtMost(usize, 1, std.math.maxInt(usize));
    }

    for (keys) |key| {
        try btree.put(key, key - 1);
    }
    std.sort.block(usize, &keys, {}, std.sort.asc(usize));

    const kvp_smallest = btree.getSmallestPtr();
    try expectEqual(kvp_smallest.?.key.*, keys[0]);
    try expectEqual(kvp_smallest.?.value.*, keys[0] - 1);
}

test "btree: getLargest" {
    var prng = std.Random.DefaultPrng.init(10);
    var random = prng.random();

    var btree: BtreeType = undefined;
    try btree.init(4, testing.allocator);
    defer btree.deinit();

    var keys: [100]usize = undefined;
    for (0..keys.len) |i| {
        keys[i] = random.intRangeAtMost(usize, 1, std.math.maxInt(usize));
    }

    for (keys) |key| {
        try btree.put(key, key - 1);
    }
    std.sort.block(usize, &keys, {}, std.sort.asc(usize));

    const kvp_largest = btree.getLargest();
    try expectEqual(kvp_largest, BtreeType.KeyValuePair{ .key = keys[99], .value = keys[99] - 1 });
}

test "btree: getLargestPtr" {
    var prng = std.Random.DefaultPrng.init(10);
    var random = prng.random();

    var btree: BtreeType = undefined;
    try btree.init(4, testing.allocator);
    defer btree.deinit();

    var keys: [100]usize = undefined;
    for (0..keys.len) |i| {
        keys[i] = random.intRangeAtMost(usize, 1, std.math.maxInt(usize));
    }

    for (keys) |key| {
        try btree.put(key, key - 1);
    }
    std.sort.block(usize, &keys, {}, std.sort.asc(usize));

    const kvp_largest = btree.getLargestPtr();
    try expectEqual(kvp_largest.?.key.*, keys[99]);
    try expectEqual(kvp_largest.?.value.*, keys[99] - 1);
}
