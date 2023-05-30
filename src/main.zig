const std = @import("std");
const testing = std.testing;

const copy = std.mem.copy;
const asBytes = std.mem.asBytes;

pub const Cmp = enum {
    Smaller,
    Equal,
    Greater,
};

pub const Color = enum(u8) {
    Red = 1,
    Black = 0,
};

pub const Dir = enum {
    Left,
    Right,
};

/// Red-black tree in linear memory
///
/// A red-black tree is a balanced binary search tree that satisfies the following requirements:
/// 1. Every node is either red or black
/// 2. All null nodes are considered black
/// 3. A red node does not have a red child
/// 4. Every path from a given node to any of its descendant null nodes goes through the same number of black nodes
pub fn RBTree(
    /// The type of a node key
    comptime K: type,
    /// The type of a node value
    comptime V: type,
    /// A function for comparing two keys
    comptime cmp: fn (lhs: *const K, rhs: *const K) Cmp,
) type {
    return struct {
        const KEY_SIZE: usize = @sizeOf(K);
        const VALUE_SIZE: usize = @sizeOf(V);
        const COLOR_SIZE: usize = @sizeOf(Color);
        const INDEX_SIZE: usize = @sizeOf(?usize);
        const NODE_SIZE: usize = KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE * 3;
        const KEY_INDEX: usize = 0;
        const VALUE_INDEX: usize = KEY_SIZE;
        const COLOR_INDEX: usize = KEY_SIZE + VALUE_SIZE;
        const PARENT_INDEX: usize = KEY_SIZE + VALUE_SIZE + COLOR_SIZE;
        const LCHILD_INDEX: usize = KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE;
        const RCHILD_INDEX: usize = KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE * 2;

        const Self = @This();

        /// An array of bytes representing the memory for the tree nodes
        raw: []u8,
        /// The number of nodes currently stored in the tree
        count: usize = 0,
        max: usize = 0,
        allocator: std.mem.Allocator,

        // +++++++++++++++++++++++++++++++++++++
        // Public
        // +++++++++++++++++++++++++++++++++++++

        pub fn init(allocator: std.mem.Allocator) !Self {
            return Self{
                .raw = try allocator.alloc(u8, NODE_SIZE * 12),
                .count = 0,
                .max = 12,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            self.allocator.free(self.raw);
        }

        /// Searches the tree for a node with the specified key k and returns its index
        /// if found, or null if not found
        pub fn get(self: *const Self, k: K) ?usize {
            if (self.count == 0) return null;

            var node: usize = 0; // we start at the root node
            while (true) {
                const nk = self.get_key(node).?;
                switch (cmp(&k, &nk)) {
                    .Smaller => {
                        // k is smaller than nk
                        node = if (self.get_child(node, .Left)) |child| blk: {
                            break :blk child;
                        } else {
                            return null;
                        };
                    },
                    .Equal => {
                        return node;
                    },
                    .Greater => {
                        // k is greater than nk
                        node = if (self.get_child(node, .Right)) |child| blk: {
                            break :blk child;
                        } else {
                            return null;
                        };
                    },
                }
            }
        }

        /// Retrieves the key of the node at index idx in the tree
        pub fn get_key(self: *const Self, node: ?usize) ?K {
            if (node) |idx| {
                const offset = ioffset(idx);
                var raw_key: [KEY_SIZE]u8 = undefined;
                @memcpy(raw_key[0..], self.raw[offset .. offset + KEY_SIZE]);
                return std.mem.bytesToValue(K, &raw_key);
            } else {
                return null;
            }
        }

        /// Retrieves the value of the node at index idx in the tree
        pub fn get_value(self: *const Self, node: ?usize) ?V {
            if (node) |idx| {
                var offset = ioffset(idx) + VALUE_INDEX;
                var raw_value: [VALUE_SIZE]u8 = undefined;
                @memcpy(raw_value[0..], self.raw[offset .. offset + VALUE_SIZE]);
                return std.mem.bytesToValue(V, &raw_value);
            } else {
                return null;
            }
        }

        /// Inserts a new node with key k and value v into the tree
        pub fn insert(self: *Self, k: K, v: V) !void {
            // Find free spot
            var parent: ?usize = null; // we start at the root node
            var grand_parent: ?usize = null;
            var uncle: ?usize = null;
            var side: ?Dir = null;
            var dir: Dir = .Left;

            if (self.count > 0) {
                parent = 0;
                while (true) {
                    const nk = self.get_key(parent).?;
                    switch (cmp(&k, &nk)) {
                        .Smaller => {
                            // k is smaller than nk
                            if (self.get_child(parent, .Left)) |child| {
                                grand_parent = parent;
                                parent = child;
                            } else {
                                side = .Left;
                                break;
                            }
                        },
                        .Equal => {
                            return; // TODO
                        },
                        .Greater => {
                            // k is greater than nk
                            if (self.get_child(parent, .Right)) |child| {
                                grand_parent = parent;
                                parent = child;
                            } else {
                                side = .Right;
                                break;
                            }
                        },
                    }
                }
            }

            // Insert node; the node becomes a child of the given parent
            var node = self.count;
            try self.add(node, k, v, Color.Red, parent, null, null);
            self.count += 1;
            if (side) |_side| {
                self.set_child(parent, node, _side);
            } else {
                // Insertion complete
                return;
            }

            while (true) {
                if (self.get_color(parent) == .Black) {
                    // The current node’s parent P is black, so requirement 3 holds.
                    // Requirement 4 holds also according to the loop invariant.
                    return;
                }

                grand_parent = if (self.get_parent(parent)) |gp| blk: {
                    break :blk gp;
                } else { // parent is root and red
                    self.set_color(parent, .Black);
                    return;
                };

                // Get the side of grand parent on which the parent is located
                const parent_side = self.get_child(grand_parent, .Left);
                dir = if (parent_side != null and parent_side.? == parent) .Left else .Right;
                uncle = self.get_other_child(grand_parent, dir);

                if (self.get_color(uncle) == .Black) {
                    // Parent is red and uncle is black
                    const other_child = self.get_other_child(parent, dir);
                    if (other_child != null and other_child.? == node) {
                        _ = self.rotate_dir_root(parent, dir); // parent is never the root
                        node = parent.?; // new current node
                        parent = self.get_child(grand_parent, dir).?; // new parent of node
                    }
                    _ = self.rotate_dir_root(grand_parent, if (dir == .Left) .Right else .Left); // grand parent may be root
                    self.set_color(parent, .Black);
                    self.set_color(grand_parent, .Red);
                    return;
                }

                self.set_color(parent, .Black);
                self.set_color(uncle, .Black);
                self.set_color(grand_parent, .Red);
                node = grand_parent.?; // new current node

                parent = if (self.get_parent(node)) |p| blk: {
                    break :blk p;
                } else {
                    break;
                };
            }
            return;
        }

        // +++++++++++++++++++++++++++++++++++++
        // Private
        // +++++++++++++++++++++++++++++++++++++

        /// Retrieves the color (Red or Black) of the node at index idx in the tree
        fn get_color(self: *const Self, node: ?usize) Color {
            if (node) |idx| {
                var offset = ioffset(idx) + COLOR_INDEX;
                return @intToEnum(Color, self.raw[offset]);
            } else {
                return .Black;
            }
        }

        /// Retrieves the index of the parent node of the node at index idx in the tree
        fn get_parent(self: *const Self, node: ?usize) ?usize {
            if (node) |idx| {
                var offset = ioffset(idx) + PARENT_INDEX;
                var raw_idx: [INDEX_SIZE]u8 = undefined;
                @memcpy(raw_idx[0..], self.raw[offset .. offset + INDEX_SIZE]);
                return std.mem.bytesToValue(?usize, &raw_idx);
            } else {
                return null;
            }
        }

        /// Retrieves the index of the child node in the specified dir
        /// (either left or right) of the node at index idx in the tree
        fn get_child(self: *const Self, node: ?usize, dir: Dir) ?usize {
            if (node) |idx| {
                const addend = if (dir == .Left) LCHILD_INDEX else RCHILD_INDEX;
                var offset = ioffset(idx) + addend;
                var raw_idx: [INDEX_SIZE]u8 = undefined;
                @memcpy(raw_idx[0..], self.raw[offset .. offset + INDEX_SIZE]);
                return std.mem.bytesToValue(?usize, &raw_idx);
            } else {
                return null;
            }
        }

        /// Retrieves the index of the child node in the opposite direction of the
        /// specified dir (either left or right) of the node at index idx in the tree
        fn get_other_child(self: *const Self, node: ?usize, dir: Dir) ?usize {
            return self.get_child(node, if (dir == .Left) .Right else .Left);
        }

        fn set_key(self: *Self, node: ?usize, key: K) void {
            if (node) |idx| {
                var offset = ioffset(idx);
                std.mem.copy(u8, self.raw[offset .. offset + KEY_SIZE], std.mem.asBytes(&key));
            } else {
                return;
            }
        }

        fn set_value(self: *Self, node: ?usize, value: V) void {
            if (node) |idx| {
                var offset = ioffset(idx) + VALUE_INDEX;
                std.mem.copy(u8, self.raw[offset .. offset + VALUE_SIZE], std.mem.asBytes(&value));
            } else {
                return;
            }
        }

        fn set_color(self: *Self, node: ?usize, color: Color) void {
            if (node) |idx| {
                var offset = ioffset(idx) + COLOR_INDEX;
                std.mem.copy(u8, self.raw[offset .. offset + COLOR_SIZE], std.mem.asBytes(&color));
            } else {
                return;
            }
        }

        fn set_parent(self: *Self, node: ?usize, parent: ?usize) void {
            if (node) |idx| {
                var offset = ioffset(idx) + PARENT_INDEX;
                std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&parent));
            } else {
                return;
            }
        }

        fn set_child(self: *Self, node: ?usize, child: ?usize, dir: Dir) void {
            if (node) |idx| {
                const addend = if (dir == .Left) LCHILD_INDEX else RCHILD_INDEX;
                var offset = ioffset(idx) + addend;
                std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&child));
            } else {
                return;
            }
        }

        /// Performs a rotation in the specified dir (either left or right) on the
        /// node at index p in the tree t, making the rotated node the new root of
        /// the subtree and returning its index
        fn rotate_dir_root(t: *Self, root: ?usize, dir: Dir) ?usize {
            if (root == null) return null;
            const p = root.?;
            const g: ?usize = t.get_parent(p);
            var s: ?usize = t.get_other_child(p, dir);
            if (s == null) return p; // pointer to true node required!
            const c: ?usize = t.get_child(s.?, dir);

            t.set_child(p, c, if (dir == .Left) .Right else .Left);
            t.set_parent(c, p);

            if (g) |_g| {
                t.set_child(s, p, dir);
                t.set_parent(p, s);
                t.set_parent(s, _g);

                const rchild = t.get_child(_g, .Right);
                const _dir: Dir = if (rchild != null and rchild == p) .Right else .Left;
                t.set_child(_g, s, _dir);
            } else {
                // The first element is always the root, i.e.
                // we must swap the current root with s so it
                // can become the new root of the tree
                t.swap(0, s);
                t.set_child(0, s, dir);
                t.set_parent(s, null);
                s = 0;
            }

            return s.?; // s is the new root of the subtree
        }

        inline fn ioffset(node: usize) usize {
            return NODE_SIZE * node;
        }

        /// Add a node at the specified index to linear memory
        fn add(
            self: *Self,
            idx: usize,
            key: K,
            value: V,
            color: Color,
            parent: ?usize,
            lchild: ?usize,
            rchild: ?usize,
        ) !void {
            if (idx >= self.max) try self.expand();

            var offset = NODE_SIZE * idx;
            copy(u8, self.raw[offset + KEY_INDEX .. offset + KEY_INDEX + KEY_SIZE], asBytes(&key));
            copy(u8, self.raw[offset + VALUE_INDEX .. offset + VALUE_INDEX + VALUE_SIZE], asBytes(&value));
            copy(u8, self.raw[offset + COLOR_INDEX .. offset + COLOR_INDEX + COLOR_SIZE], asBytes(&color));
            copy(u8, self.raw[offset + PARENT_INDEX .. offset + PARENT_INDEX + INDEX_SIZE], asBytes(&parent));
            copy(u8, self.raw[offset + LCHILD_INDEX .. offset + LCHILD_INDEX + INDEX_SIZE], asBytes(&lchild));
            copy(u8, self.raw[offset + RCHILD_INDEX .. offset + RCHILD_INDEX + INDEX_SIZE], asBytes(&rchild));
        }

        fn expand(self: *Self) !void {
            const EXPAND_SIZE = 12;
            // TODO: the size is currently arbitrary
            const current_size = self.raw.len;
            const new_size = self.raw.len + NODE_SIZE * EXPAND_SIZE;
            var mem = try self.allocator.alloc(u8, new_size);
            copy(u8, mem[0..current_size], self.raw[0..]);
            self.allocator.free(self.raw);
            self.raw = mem;
            self.max = self.max + EXPAND_SIZE;
        }

        /// The swap function swaps the positions of two nodes in the RBTree
        fn swap(self: *Self, x: ?usize, y: ?usize) void {
            if (x == null or y == null) return;
            var offset1 = ioffset(x.?);
            var offset2 = ioffset(y.?);
            var buffer: [NODE_SIZE]u8 = undefined;
            @memcpy(buffer[0..], self.raw[offset1 .. offset1 + NODE_SIZE]);

            if (self.get_parent(x)) |p| {
                if (self.get_child(p, .Left) != null) {
                    self.set_child(p, y, .Left);
                } else {
                    self.set_child(p, y, .Right);
                }
            }
            self.set_parent(self.get_child(x, .Left), y);
            self.set_parent(self.get_child(x, .Right), y);

            if (self.get_parent(y)) |p| {
                if (self.get_child(p, .Left) != null) {
                    self.set_child(p, x, .Left);
                } else {
                    self.set_child(p, x, .Right);
                }
            }
            self.set_parent(self.get_child(y, .Left), x);
            self.set_parent(self.get_child(y, .Right), x);

            @memcpy(self.raw[offset1 .. offset1 + NODE_SIZE], self.raw[offset2 .. offset2 + NODE_SIZE]);
            @memcpy(self.raw[offset2 .. offset2 + NODE_SIZE], buffer[0..]);
        }

        pub fn print_tree(self: *const Self) void {
            std.debug.print("\n", .{});
            if (self.count > 0) {
                self.print_tree_helper(0, 0);
            }
            std.debug.print("\n", .{});
        }

        fn print_tree_helper(self: *const Self, node: usize, indent: isize) void {
            const INDENT_STEP = 4;

            if (self.get_child(node, .Right)) |child| {
                self.print_tree_helper(child, indent + INDENT_STEP);
            }

            var i: isize = 0;
            while (i < indent) : (i += 1) {
                std.debug.print(" ", .{});
            }
            if (self.get_color(node) == .Black) {
                std.debug.print("{any}\n", .{self.get_key(node).?});
            } else {
                std.debug.print("<{any}>\n", .{self.get_key(node).?});
            }

            if (self.get_child(node, .Left)) |child| {
                self.print_tree_helper(child, indent + INDENT_STEP);
            }
        }
    };
}

const NodeDesc = struct {
    k: u32,
    v: u32,
    color: Color,
    parent: ?u32,
    lchild: ?u32,
    rchild: ?u32,
};

fn verify_tree(tree: anytype, desc: []const NodeDesc) !void {
    for (desc) |nd| {
        const idx = if (tree.get(nd.k)) |idx| idx else return error.NotFound;
        try std.testing.expectEqual(nd.k, tree.get_key(idx).?);
        try std.testing.expectEqual(nd.v, tree.get_value(idx).?);
        try std.testing.expectEqual(nd.color, tree.get_color(idx));
        try std.testing.expectEqual(nd.parent, tree.get_key(tree.get_parent(idx)));
        try std.testing.expectEqual(nd.lchild, tree.get_key(tree.get_child(idx, .Left)));
        try std.testing.expectEqual(nd.rchild, tree.get_key(tree.get_child(idx, .Right)));
    }
}

test "add node to linear memory" {
    const allocator = testing.allocator;
    const S = struct {
        pub fn cmp(lhs: *const u32, rhs: *const u32) Cmp {
            if (lhs.* == rhs.*) {
                return .Equal;
            } else if (lhs.* < rhs.*) {
                return .Smaller;
            } else {
                return .Greater;
            }
        }
    };

    const Tree = RBTree(u32, u32, S.cmp);
    var tree = try Tree.init(allocator);
    defer tree.deinit();

    try tree.add(0, 10, 100, Color.Black, null, null, null);
    tree.count += 1;

    try verify_tree(&tree, &.{
        NodeDesc{ .k = 10, .v = 100, .color = .Black, .parent = null, .lchild = null, .rchild = null },
    });
}

test "Rotate Node in RBTree right" {
    const allocator = testing.allocator;
    const S = struct {
        pub fn cmp(lhs: *const u32, rhs: *const u32) Cmp {
            if (lhs.* == rhs.*) {
                return .Equal;
            } else if (lhs.* < rhs.*) {
                return .Smaller;
            } else {
                return .Greater;
            }
        }
    };

    const Tree = RBTree(u32, u32, S.cmp);
    var tree = try Tree.init(allocator);
    defer tree.deinit();

    // Add nodes to the tree
    //                    10
    //                   /  \
    //                  5   15
    //                 / \  / \
    //               nil 3  7 nil
    try tree.add(0, 10, 100, Color.Black, null, 1, 2); // root node
    try tree.add(1, 5, 50, Color.Red, null, null, 3);
    try tree.add(2, 15, 150, Color.Red, null, 4, null);
    try tree.add(3, 3, 30, Color.Black, 1, null, null);
    try tree.add(4, 7, 70, Color.Black, 2, null, null);
    tree.count = 5;

    const newRoot = tree.rotate_dir_root(0, .Right);
    _ = newRoot;

    try verify_tree(&tree, &.{
        NodeDesc{ .k = 5, .v = 50, .color = .Red, .parent = null, .lchild = null, .rchild = 10 },
    });
}

test "Get node index" {
    const allocator = testing.allocator;
    const S = struct {
        pub fn cmp(lhs: *const u32, rhs: *const u32) Cmp {
            if (lhs.* == rhs.*) {
                return .Equal;
            } else if (lhs.* < rhs.*) {
                return .Smaller;
            } else {
                return .Greater;
            }
        }
    };

    const Tree = RBTree(u32, u32, S.cmp);
    var tree = try Tree.init(allocator);
    defer tree.deinit();

    // Add nodes to the tree
    //                    10
    //                   /  \
    //                  5   15
    //                 / \  / \
    //                3  7 nil nil
    try tree.add(0, 10, 100, Color.Black, null, 1, 2); // root node
    try tree.add(1, 5, 50, Color.Red, null, 3, 4);
    try tree.add(2, 15, 150, Color.Red, null, null, null);
    try tree.add(3, 3, 30, Color.Black, 1, null, null);
    try tree.add(4, 7, 70, Color.Black, 2, null, null);
    tree.count = 5;

    // Find nodes in tree
    try testing.expectEqual(@intCast(usize, 0), tree.get(10).?);
    try testing.expectEqual(@intCast(usize, 1), tree.get(5).?);
    try testing.expectEqual(@intCast(usize, 2), tree.get(15).?);
    try testing.expectEqual(@intCast(usize, 3), tree.get(3).?);
    try testing.expectEqual(@intCast(usize, 4), tree.get(7).?);
}

test "Insert nodes" {
    const allocator = testing.allocator;
    const S = struct {
        pub fn cmp(lhs: *const u32, rhs: *const u32) Cmp {
            if (lhs.* == rhs.*) {
                return .Equal;
            } else if (lhs.* < rhs.*) {
                return .Smaller;
            } else {
                return .Greater;
            }
        }
    };

    const Tree = RBTree(u32, u32, S.cmp);
    var tree = try Tree.init(allocator);
    defer tree.deinit();

    try tree.insert(10, 100);

    try verify_tree(&tree, &.{
        NodeDesc{ .k = 10, .v = 100, .color = .Red, .parent = null, .lchild = null, .rchild = null },
    });

    try tree.insert(5, 50);

    try verify_tree(&tree, &.{
        NodeDesc{ .k = 10, .v = 100, .color = .Black, .parent = null, .lchild = 5, .rchild = null },
        NodeDesc{ .k = 5, .v = 50, .color = .Red, .parent = 10, .lchild = null, .rchild = null },
    });

    try tree.insert(15, 150);

    try verify_tree(&tree, &.{
        NodeDesc{ .k = 10, .v = 100, .color = .Black, .parent = null, .lchild = 5, .rchild = 15 },
        NodeDesc{ .k = 5, .v = 50, .color = .Red, .parent = 10, .lchild = null, .rchild = null },
        NodeDesc{ .k = 15, .v = 150, .color = .Red, .parent = 10, .lchild = null, .rchild = null },
    });

    try tree.insert(3, 30);

    try verify_tree(&tree, &.{
        NodeDesc{ .k = 10, .v = 100, .color = .Red, .parent = null, .lchild = 5, .rchild = 15 },
        NodeDesc{ .k = 5, .v = 50, .color = .Black, .parent = 10, .lchild = 3, .rchild = null },
        NodeDesc{ .k = 15, .v = 150, .color = .Black, .parent = 10, .lchild = null, .rchild = null },
        NodeDesc{ .k = 3, .v = 30, .color = .Red, .parent = 5, .lchild = null, .rchild = null },
    });

    try tree.insert(7, 70);

    try verify_tree(&tree, &.{
        NodeDesc{ .k = 10, .v = 100, .color = .Red, .parent = null, .lchild = 5, .rchild = 15 },
        NodeDesc{ .k = 5, .v = 50, .color = .Black, .parent = 10, .lchild = 3, .rchild = 7 },
        NodeDesc{ .k = 15, .v = 150, .color = .Black, .parent = 10, .lchild = null, .rchild = null },
        NodeDesc{ .k = 3, .v = 30, .color = .Red, .parent = 5, .lchild = null, .rchild = null },
        NodeDesc{ .k = 7, .v = 70, .color = .Red, .parent = 5, .lchild = null, .rchild = null },
    });

    try tree.insert(11, 110);
    try tree.insert(8, 80);

    try verify_tree(&tree, &.{
        NodeDesc{ .k = 10, .v = 100, .color = .Black, .parent = null, .lchild = 5, .rchild = 15 },
        NodeDesc{ .k = 5, .v = 50, .color = .Red, .parent = 10, .lchild = 3, .rchild = 7 },
        NodeDesc{ .k = 15, .v = 150, .color = .Black, .parent = 10, .lchild = 11, .rchild = null },
        NodeDesc{ .k = 3, .v = 30, .color = .Black, .parent = 5, .lchild = null, .rchild = null },
        NodeDesc{ .k = 7, .v = 70, .color = .Black, .parent = 5, .lchild = null, .rchild = 8 },
        NodeDesc{ .k = 11, .v = 110, .color = .Red, .parent = 15, .lchild = null, .rchild = null },
        NodeDesc{ .k = 8, .v = 80, .color = .Red, .parent = 7, .lchild = null, .rchild = null },
    });

    try tree.insert(12, 120);

    try verify_tree(&tree, &.{
        NodeDesc{ .k = 10, .v = 100, .color = .Black, .parent = null, .lchild = 5, .rchild = 12 },
        NodeDesc{ .k = 5, .v = 50, .color = .Red, .parent = 10, .lchild = 3, .rchild = 7 },
        NodeDesc{ .k = 15, .v = 150, .color = .Red, .parent = 12, .lchild = null, .rchild = null },
        NodeDesc{ .k = 3, .v = 30, .color = .Black, .parent = 5, .lchild = null, .rchild = null },
        NodeDesc{ .k = 7, .v = 70, .color = .Black, .parent = 5, .lchild = null, .rchild = 8 },
        NodeDesc{ .k = 11, .v = 110, .color = .Red, .parent = 12, .lchild = null, .rchild = null },
        NodeDesc{ .k = 8, .v = 80, .color = .Red, .parent = 7, .lchild = null, .rchild = null },
        NodeDesc{ .k = 12, .v = 120, .color = .Black, .parent = 10, .lchild = 11, .rchild = 15 },
    });
}
