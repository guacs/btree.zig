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

        const Node = struct {
            keys: KeyArray,
            values: ValueArray,
            // Only for internal nodes.
            children: ChildrenArray,

            fn initLeafNode(self: *Node, keys_max: usize, allocator: Allocator) !void {
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

            inline fn splitInternal(self: *Node, allocator: Allocator) !SplitResult {
                const pivot_idx = self.len() / 2 + 1;
                var new_node: Node = undefined;
                try new_node.initInternalNode(self.keys.items.len, allocator);

                splitArrayListAssumeCapacity(KeyT, &self.keys, &new_node.keys, pivot_idx);
                splitArrayListAssumeCapacity(ValueT, &self.values, &new_node.values, pivot_idx);
                splitArrayListAssumeCapacity(Node, &self.children, &new_node.children, pivot_idx);

                return .{ .key = self.keys.pop(), .value = self.values.pop(), .new_node = new_node };
            }

            inline fn len(self: *const Node) usize {
                return self.keys.items.len;
            }

            inline fn isFull(self: *const Node) bool {
                return self.keys.items.len == self.keys.capacity;
            }

            inline fn isLeaf(self: *const Node) bool {
                return self.children.items.len == 0;
            }

            /// Free the memory used by this node and all it's children.
            fn deinit(self: *Node, allocator: Allocator) void {
                self.keys.deinit(allocator);
                self.values.deinit(allocator);

                for (self.children.items) |*child| {
                    child.deinit(allocator);
                }

                self.children.deinit(allocator);
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

        len: usize = 0,

        degree: u16,
        root: Node = undefined,
        depth: usize = 1,

        allocator: std.mem.Allocator,

        pub fn init(self: *Self, degree: u16, allocator: Allocator) !void {
            self.* = .{
                .degree = degree,
                .allocator = allocator,
            };
            try self.root.initLeafNode(2 * degree - 1, allocator);
        }

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

        pub fn deinit(self: *Self) void {
            self.root.deinit(self.allocator);
        }

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
    try expectEqual(btree.root.values.items.len, btree.root.keys.items.len);
    if (btree.root.isLeaf() == false) {
        try testing.expectEqual(btree.root.children.items.len, btree.root.keys.items.len + 1);

        for (btree.root.children.items) |*node| {
            try validateNode(node, btree.degree);
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
    if (node.isLeaf() == false) {
        try testing.expectEqual(node.children.items.len, node.keys.items.len + 1);

        for (node.children.items) |*child| {
            try validateNode(child, degree);
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
