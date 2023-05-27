const std = @import("std");
const testing = std.testing;

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

pub fn RBTree(
    comptime K: type,
    comptime V: type,
    comptime max: usize,
    comptime cmp: *const fn (lhs: *const K, rhs: *const K) Cmp,
) type {
    _ = cmp;
    return struct {
        const KEY_SIZE: usize = @sizeOf(K);
        const VALUE_SIZE: usize = @sizeOf(V);
        const COLOR_SIZE: usize = @sizeOf(Color);
        const INDEX_SIZE: usize = @sizeOf(usize);
        const NODE_SIZE: usize = KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE * 3;
        const TOTAL_SIZE: usize = NODE_SIZE * max;

        const MAX: usize = max;
        const Self = @This();

        raw: [TOTAL_SIZE]u8 = .{0} ** TOTAL_SIZE,
        count: usize = 0,

        pub fn rotate_left(t: *Self, n: usize) void {
            _ = rotate_dir_root(t, n, .Left);
        }

        pub fn rotate_right(t: *Self, n: usize) void {
            _ = rotate_dir_root(t, n, .Right);
        }

        pub fn rotate_dir_root(t: *Self, p: usize, dir: Dir) usize {
            const g: ?usize = if (p > 0) t.get_parent(p) else null;
            var s: usize = switch (dir) {
                .Left => t.get_rchild(p),
                .Right => t.get_lchild(p),
            };
            if (s == 0) return p; // pointer to true node required!
            const c: usize = switch (dir) {
                .Left => t.get_lchild(s),
                .Right => t.get_rchild(s),
            };

            switch (dir) {
                .Left => t.set_rchild(p, c),
                .Right => t.set_lchild(p, c),
            }
            if (c != 0) t.set_parent(c, p);

            if (g) |_g| {
                switch (dir) {
                    .Left => t.set_lchild(s, p),
                    .Right => t.set_rchild(s, p),
                }
                t.set_parent(p, s);
                t.set_parent(s, _g);
                const _dir: Dir = if (p == t.get_rchild(_g)) .Right else .Left;
                switch (_dir) {
                    .Left => t.set_lchild(_g, s),
                    .Right => t.set_rchild(_g, s),
                }
            } else {
                // The first element is always the root, i.e.
                // we must swap the current root with s so it
                // can become the new root of the tree
                t.swap(0, s);

                switch (dir) {
                    .Left => t.set_lchild(0, s),
                    .Right => t.set_rchild(0, s),
                }
                t.set_parent(s, 0);
                s = 0;
            }

            return s; // s is the new root of the subtree
        }

        pub fn get_key(self: *Self, idx: usize) K {
            const offset = NODE_SIZE * idx;
            var raw_key: [KEY_SIZE]u8 = undefined;
            @memcpy(raw_key[0..], self.raw[offset .. offset + KEY_SIZE]);
            return std.mem.bytesToValue(K, &raw_key);
        }

        pub fn get_value(self: *Self, idx: usize) V {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE;
            var raw_value: [VALUE_SIZE]u8 = undefined;
            @memcpy(raw_value[0..], self.raw[offset .. offset + VALUE_SIZE]);
            return std.mem.bytesToValue(V, &raw_value);
        }

        pub fn get_color(self: *Self, idx: usize) Color {
            var offset = NODE_SIZE * idx;
            return @intToEnum(Color, self.raw[offset + KEY_SIZE + VALUE_SIZE]);
        }

        pub fn get_parent(self: *Self, idx: usize) usize {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE;
            var raw_idx: [INDEX_SIZE]u8 = undefined;
            @memcpy(raw_idx[0..], self.raw[offset .. offset + INDEX_SIZE]);
            return std.mem.bytesToValue(usize, &raw_idx);
        }

        pub fn get_lchild(self: *Self, idx: usize) usize {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE;
            var raw_idx: [INDEX_SIZE]u8 = undefined;
            @memcpy(raw_idx[0..], self.raw[offset .. offset + INDEX_SIZE]);
            return std.mem.bytesToValue(usize, &raw_idx);
        }

        pub fn get_rchild(self: *Self, idx: usize) usize {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE * 2;
            var raw_idx: [INDEX_SIZE]u8 = undefined;
            @memcpy(raw_idx[0..], self.raw[offset .. offset + INDEX_SIZE]);
            return std.mem.bytesToValue(usize, &raw_idx);
        }

        pub fn set_parent(self: *Self, idx: usize, p: usize) void {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&p));
        }

        pub fn set_lchild(self: *Self, idx: usize, lc: usize) void {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&lc));
        }

        pub fn set_rchild(self: *Self, idx: usize, rc: usize) void {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE * 2;
            std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&rc));
        }

        pub fn swap(self: *Self, x: usize, y: usize) void {
            var offset1 = NODE_SIZE * x;
            var offset2 = NODE_SIZE * y;
            var buffer: [NODE_SIZE]u8 = undefined;
            @memcpy(buffer[0..], self.raw[offset1 .. offset1 + NODE_SIZE]);
            @memcpy(self.raw[offset1 .. offset1 + NODE_SIZE], self.raw[offset2 .. offset2 + NODE_SIZE]);
            @memcpy(self.raw[offset2 .. offset2 + NODE_SIZE], buffer[0..]);
        }

        /// Add a node at the specified index to linear memory
        ///
        /// DO NOT USE TO INSERT NODES!
        pub fn add(
            self: *Self,
            idx: usize,
            key: K,
            value: V,
            color: Color,
            parent: usize,
            lchild: usize,
            rchild: usize,
        ) void {
            if (idx >= MAX) return;

            var offset = NODE_SIZE * idx;
            std.mem.copy(u8, self.raw[offset .. offset + KEY_SIZE], std.mem.asBytes(&key));
            offset += KEY_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + VALUE_SIZE], std.mem.asBytes(&value));
            offset += VALUE_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + COLOR_SIZE], std.mem.asBytes(&color));
            offset += COLOR_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&parent));
            offset += INDEX_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&lchild));
            offset += INDEX_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&rchild));
        }
    };
}

test "add node to linear memory" {
    const S = struct {
        pub fn cmp(lhs: *const [16]u8, rhs: *const [16]u8) Cmp {
            _ = lhs;
            _ = rhs;
            return .Equal;
        }
    };

    const Tree = RBTree([16]u8, usize, 1, S.cmp);
    var tree = Tree{};

    const k: [16]u8 = .{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 };
    const v: usize = 666;
    const color: Color = Color.Black;

    tree.add(0, k, v, color, 0, 0, 0);

    const expected = "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x9a\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";

    try std.testing.expectEqualSlices(u8, expected, tree.raw[0..Tree.NODE_SIZE]);

    try std.testing.expectEqualSlices(u8, k[0..], tree.get_key(0)[0..]);
    try std.testing.expectEqual(@intCast(usize, 666), tree.get_value(0));
    try std.testing.expectEqual(Color.Black, tree.get_color(0));
    try std.testing.expectEqual(@intCast(usize, 0), tree.get_parent(0));
    try std.testing.expectEqual(@intCast(usize, 0), tree.get_lchild(0));
    try std.testing.expectEqual(@intCast(usize, 0), tree.get_rchild(0));
}

test "Rotate Node in RBTree right" {
    const S = struct {
        pub fn cmp(lhs: *const u32, rhs: *const u32) Cmp {
            _ = lhs;
            _ = rhs;
            return .Equal;
        }
    };
    const K = u32;
    const V = u32;
    const MaxNodes = 5;
    const Tree = RBTree(K, V, MaxNodes, S.cmp);
    var tree = Tree{};

    // Add nodes to the tree
    //                    10
    //                   /  \
    //                  5   15
    //                 / \  / \
    //               nil 3  7 nil
    tree.add(0, 10, 100, Color.Black, 0, 1, 2); // root node
    tree.add(1, 5, 50, Color.Red, 0, 0, 3);
    tree.add(2, 15, 150, Color.Red, 0, 4, 0);
    tree.add(3, 3, 30, Color.Black, 1, 0, 0);
    tree.add(4, 7, 70, Color.Black, 2, 0, 0);

    // Perform node rotation
    const newRoot = tree.rotate_dir_root(0, Dir.Right);

    // Verify the new root of the tree
    const expectedRoot: usize = 0;
    try testing.expectEqual(expectedRoot, newRoot);
    try testing.expectEqual(@intCast(u32, 5), tree.get_key(0));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(0));
    try testing.expectEqual(@intCast(u32, 10), tree.get_key(tree.get_rchild(0)));
    try testing.expectEqual(@intCast(u32, 3), tree.get_key(tree.get_lchild(tree.get_rchild(0))));
    try testing.expectEqual(@intCast(u32, 15), tree.get_key(tree.get_rchild(tree.get_rchild(0))));
}

test "Rotate Node in RBTree left" {
    const S = struct {
        pub fn cmp(lhs: *const u32, rhs: *const u32) Cmp {
            _ = lhs;
            _ = rhs;
            return .Equal;
        }
    };
    const K = u32;
    const V = u32;
    const MaxNodes = 5;
    const Tree = RBTree(K, V, MaxNodes, S.cmp);
    var tree = Tree{};

    // Add nodes to the tree
    //                    10
    //                   /  \
    //                  5   15
    //                 / \  / \
    //               nil 3  7 nil
    tree.add(0, 10, 100, Color.Black, 0, 1, 2); // root node
    tree.add(1, 5, 50, Color.Red, 0, 0, 3);
    tree.add(2, 15, 150, Color.Red, 0, 4, 0);
    tree.add(3, 3, 30, Color.Black, 1, 0, 0);
    tree.add(4, 7, 70, Color.Black, 2, 0, 0);

    // Perform node rotation
    const newRoot = tree.rotate_dir_root(0, Dir.Left);

    // Verify the new root of the tree
    const expectedRoot: usize = 0;
    try testing.expectEqual(expectedRoot, newRoot);
    try testing.expectEqual(@intCast(u32, 15), tree.get_key(0));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(0));
    try testing.expectEqual(@intCast(u32, 10), tree.get_key(tree.get_lchild(0)));
    try testing.expectEqual(@intCast(u32, 7), tree.get_key(tree.get_rchild(tree.get_lchild(0))));
    try testing.expectEqual(@intCast(u32, 5), tree.get_key(tree.get_lchild(tree.get_lchild(0))));
}

test "Rotate Node with Key 15 to the Right" {
    const S = struct {
        pub fn cmp(lhs: *const u32, rhs: *const u32) Cmp {
            _ = lhs;
            _ = rhs;
            return .Equal;
        }
    };
    const K = u32;
    const V = u32;
    const MaxNodes = 5;
    const Tree = RBTree(K, V, MaxNodes, S.cmp);
    var tree = Tree{};

    // Add nodes to the tree
    //                    10
    //                   /  \
    //                  5   15
    //                 / \  / \
    //               nil 3  7 nil
    tree.add(0, 10, 100, Color.Black, 0, 1, 2); // root node
    tree.add(1, 5, 50, Color.Red, 0, 0, 3);
    tree.add(2, 15, 150, Color.Red, 0, 4, 0);
    tree.add(3, 3, 30, Color.Black, 1, 0, 0);
    tree.add(4, 7, 70, Color.Black, 2, 0, 0);

    // Perform node rotation
    const newRoot = tree.rotate_dir_root(2, Dir.Right);

    // Verify the new root of the tree
    const expectedRoot: usize = 4;
    try testing.expectEqual(expectedRoot, newRoot);
    try testing.expectEqual(@intCast(u32, 7), tree.get_key(4));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(4));
    try testing.expectEqual(@intCast(usize, 0), tree.get_parent(4));
    try testing.expectEqual(@intCast(u32, 15), tree.get_key(tree.get_rchild(4)));
    try testing.expectEqual(@intCast(usize, 4), tree.get_parent(2));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(2));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(2));
}
