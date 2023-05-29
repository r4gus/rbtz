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
    /// The maximum number of nodes the tree can store
    comptime max: usize,
    /// A function for comparing two keys
    comptime cmp: fn (lhs: *const K, rhs: *const K) Cmp,
) type {
    return struct {
        const KEY_SIZE: usize = @sizeOf(K);
        const VALUE_SIZE: usize = @sizeOf(V);
        const COLOR_SIZE: usize = @sizeOf(Color);
        const INDEX_SIZE: usize = @sizeOf(usize);
        const NODE_SIZE: usize = KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE * 3;
        const TOTAL_SIZE: usize = NODE_SIZE * max;

        const MAX: usize = max;
        const Self = @This();

        /// An array of bytes representing the memory for the tree nodes
        raw: [TOTAL_SIZE]u8 = .{0} ** TOTAL_SIZE,
        /// The number of nodes currently stored in the tree
        count: usize = 0,

        /// Searches the tree for a node with the specified key k and returns its index
        /// if found, or null if not found
        pub fn get(self: *const Self, k: K) ?usize {
            if (self.count == 0) return null;

            var node: usize = 0; // we start at the root node
            while (true) {
                const nk = self.get_key(node);
                switch (cmp(&k, &nk)) {
                    .Smaller => {
                        // k is smaller than nk
                        node = self.get_lchild(node);
                        if (node == 0) return null;
                    },
                    .Equal => {
                        return node;
                    },
                    .Greater => {
                        // k is greater than nk
                        node = self.get_rchild(node);
                        if (node == 0) return null;
                    },
                }
            }
        }

        /// Inserts a new node with key k and value v into the tree
        pub fn insert(self: *Self, k: K, v: V) void {
            // Find free spot
            var parent: usize = 0; // we start at the root node
            var grand_parent: usize = 0;
            var uncle: usize = 0;
            var side: ?Dir = null;
            var dir: Dir = .Left;

            if (self.count > 0) {
                while (true) {
                    const nk = self.get_key(parent);
                    switch (cmp(&k, &nk)) {
                        .Smaller => {
                            // k is smaller than nk
                            const l = self.get_lchild(parent);
                            if (l == 0) {
                                side = .Left;
                                break;
                            }
                            grand_parent = parent;
                            parent = l;
                        },
                        .Equal => {
                            return; // TODO
                        },
                        .Greater => {
                            // k is greater than nk
                            const r = self.get_rchild(parent);
                            if (r == 0) {
                                side = .Right;
                                break;
                            }
                            grand_parent = parent;
                            parent = r;
                        },
                    }
                }
            }

            // Insert node; the node becomes a child of the given parent
            var node = self.count;
            self.add(node, k, v, Color.Red, parent, 0, 0);
            self.count += 1;
            if (side) |_side| {
                switch (_side) {
                    .Left => self.set_lchild(parent, node),
                    .Right => self.set_rchild(parent, node),
                }
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
                dir = if (self.get_lchild(grand_parent) == parent) .Left else .Right;
                uncle = switch (dir) {
                    .Left => self.get_rchild(grand_parent),
                    .Right => self.get_lchild(grand_parent),
                };

                if (uncle == 0 or self.get_color(uncle) == .Black) {
                    // Parent is red and uncle is black
                    if (node == self.get_other_child(parent, dir)) {
                        _ = self.rotate_dir_root(parent, dir); // parent is never the root
                        node = parent; // new current node
                        parent = self.get_child(grand_parent, dir); // new parent of node
                    }
                    _ = self.rotate_dir_root(grand_parent, if (dir == .Left) .Right else .Left); // grand parent may be root
                    self.set_color(parent, .Black);
                    self.set_color(grand_parent, .Red);
                    return;
                }

                self.set_color(parent, .Black);
                self.set_color(uncle, .Black);
                self.set_color(grand_parent, .Red);
                node = grand_parent; // new current node

                parent = if (self.get_parent(node)) |p| blk: {
                    break :blk p;
                } else {
                    break;
                };
            }
            return;
        }

        pub fn delete(self: *Self, k: K) void {
            var child: usize = 0;
            var node = if (self.get(k)) |n| n else return;

            if (self.get_lchild(node) == 0 and self.get_rchild(node) == 0) {
                if (node == 0) { // root node
                    self.delete_node(node);
                } else {
                    // We swap the node with the last node in
                    // linear memory and then remove the last entry
                    self.delete_node(node);
                }
                return;
            }

            if (self.get_lchild(node) != 0 and self.get_rchild(node) != 0) {
                // Copy key and value from predecessor and then delete it instead
                const pred = self.max_node(self.get_lchild(node));
                self.set_key(node, self.get_key(pred));
                self.set_value(node, self.get_value(pred));
                node = pred;
            }

            child = if (self.get_rchild(node) == 0) self.get_lchild(node) else self.get_rchild(node);
            if (self.get_color(node) == .Black) {
                self.set_color(node, self.get_color(child));
                self.delete_case1(node);
            }
            self.replace_node(&node, &child);
            if (child == 0) {
                self.set_color(child, .Black); // root should be black
            }

            self.delete_node(node);
        }

        fn delete_case1(self: *Self, node: usize) void {
            if (node == 0) {
                return;
            } else {
                self.delete_case2(node);
            }
        }

        fn delete_case2(self: *Self, node: usize) void {
            const p = self.get_parent(node).?;
            const dir: Dir = if (self.get_lchild(p) == node) .Left else .Right;
            const sibling = self.get_other_child(p, dir);
            if (sibling != 0 and self.get_color(sibling) == .Red) {
                self.set_color(p, .Red);
                self.set_color(sibling, .Black);
                switch (dir) {
                    .Left => self.rotate_left(p),
                    .Right => self.rotate_right(p),
                }
            }
            self.delete_case3(node);
        }

        fn delete_case3(self: *Self, node: usize) void {
            const p = self.get_parent(node).?;
            const dir: Dir = if (self.get_lchild(p) == node) .Left else .Right;
            const sibling = self.get_other_child(p, dir);
            const sibling_color: Color = if (sibling == 0) .Black else self.get_color(sibling);
            const schild_l_color: Color = if (sibling != 0 and self.get_lchild(sibling) != 0) self.get_color(self.get_lchild(sibling)) else .Black;
            const schild_r_color: Color = if (sibling != 0 and self.get_rchild(sibling) != 0) self.get_color(self.get_rchild(sibling)) else .Black;

            if (self.get_color(p) == .Black and sibling_color == .Black and schild_l_color == .Black and schild_r_color == .Black) {
                if (sibling != 0) self.set_color(sibling, .Red);
                self.delete_case1(p);
            } else {
                self.delete_case4(node);
            }
        }

        fn delete_case4(self: *Self, node: usize) void {
            const p = self.get_parent(node).?;
            const dir: Dir = if (self.get_lchild(p) == node) .Left else .Right;
            const sibling = self.get_other_child(p, dir);
            const sibling_color: Color = if (sibling == 0) .Black else self.get_color(sibling);
            const schild_l_color: Color = if (sibling != 0 and self.get_lchild(sibling) != 0) self.get_color(self.get_lchild(sibling)) else .Black;
            const schild_r_color: Color = if (sibling != 0 and self.get_rchild(sibling) != 0) self.get_color(self.get_rchild(sibling)) else .Black;

            if (self.get_color(p) == .Red and sibling_color == .Black and schild_l_color == .Black and schild_r_color == .Black) {
                if (sibling != 0) self.set_color(sibling, .Red);
                self.set_color(p, .Black);
            } else {
                self.delete_case5(node);
            }
        }

        fn delete_case5(self: *Self, node: usize) void {
            const p = self.get_parent(node).?;
            const dir: Dir = if (self.get_lchild(p) == node) .Left else .Right;
            const sibling = self.get_other_child(p, dir);
            const sibling_color: Color = if (sibling == 0) .Black else self.get_color(sibling);
            const schild_l_color: Color = if (sibling != 0 and self.get_lchild(sibling) != 0) self.get_color(self.get_lchild(sibling)) else .Black;
            const schild_r_color: Color = if (sibling != 0 and self.get_rchild(sibling) != 0) self.get_color(self.get_rchild(sibling)) else .Black;

            if (dir == .Left and sibling_color == .Black and schild_l_color == .Red and schild_r_color == .Black) {
                if (sibling != 0) {
                    self.set_color(sibling, .Red);
                    if (self.get_lchild(sibling) != 0) self.set_color(self.get_lchild(sibling), .Black);
                    self.rotate_right(sibling);
                }
            } else if (dir == .Right and sibling_color == .Black and schild_l_color == .Red and schild_r_color == .Black) {
                if (sibling != 0) {
                    self.set_color(sibling, .Red);
                    if (self.get_rchild(sibling) != 0) self.set_color(self.get_rchild(sibling), .Black);
                    self.rotate_left(sibling);
                }
            }
            self.delete_case6(node);
        }

        fn delete_case6(self: *Self, node: usize) void {
            const p = self.get_parent(node).?;
            const dir: Dir = if (self.get_lchild(p) == node) .Left else .Right;
            const sibling = self.get_other_child(p, dir);

            if (sibling != 0) self.set_color(sibling, self.get_color(p));
            self.set_color(p, .Black);

            switch (dir) {
                .Left => {
                    if (sibling != 0 and self.get_rchild(sibling) != 0) {
                        self.set_color(self.get_rchild(sibling), .Black);
                    }
                    self.rotate_left(p);
                },
                .Right => {
                    if (sibling != 0 and self.get_lchild(sibling) != 0) {
                        self.set_color(self.get_lchild(sibling), .Black);
                    }
                    self.rotate_right(p);
                },
            }
        }

        fn replace_node(self: *Self, old: *usize, new: *usize) void {
            self.set_parent(new.*, if (self.get_parent(old.*)) |p| p else 0);

            if (old.* == 0) { // root node
                self.swap(old.*, new.*);
                const buf = old.*;
                old.* = new.*;
                new.* = buf;
            } else {
                const p = self.get_parent(old.*).?;

                if (self.get_lchild(p) == old.*) {
                    self.set_lchild(p, new.*);
                } else {
                    self.set_rchild(p, new.*);
                }
            }
        }

        /// Performs a left rotation on the node at index n in the tree t
        fn rotate_left(t: *Self, n: usize) void {
            _ = rotate_dir_root(t, n, .Left);
        }

        /// Performs a right rotation on the node at index n in the tree t
        fn rotate_right(t: *Self, n: usize) void {
            _ = rotate_dir_root(t, n, .Right);
        }

        /// Performs a rotation in the specified dir (either left or right) on the
        /// node at index p in the tree t, making the rotated node the new root of
        /// the subtree and returning its index
        fn rotate_dir_root(t: *Self, p: usize, dir: Dir) usize {
            const g: ?usize = t.get_parent(p);
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

        /// Retrieves the key of the node at index idx in the tree
        pub fn get_key(self: *const Self, idx: usize) K {
            const offset = NODE_SIZE * idx;
            var raw_key: [KEY_SIZE]u8 = undefined;
            @memcpy(raw_key[0..], self.raw[offset .. offset + KEY_SIZE]);
            return std.mem.bytesToValue(K, &raw_key);
        }

        /// Retrieves the value of the node at index idx in the tree
        pub fn get_value(self: *const Self, idx: usize) V {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE;
            var raw_value: [VALUE_SIZE]u8 = undefined;
            @memcpy(raw_value[0..], self.raw[offset .. offset + VALUE_SIZE]);
            return std.mem.bytesToValue(V, &raw_value);
        }

        /// Retrieves the color (Red or Black) of the node at index idx in the tree
        fn get_color(self: *const Self, idx: usize) Color {
            var offset = NODE_SIZE * idx;
            return @intToEnum(Color, self.raw[offset + KEY_SIZE + VALUE_SIZE]);
        }

        /// Retrieves the index of the parent node of the node at index idx in the tree
        fn get_parent(self: *const Self, idx: usize) ?usize {
            if (idx == 0) return null; // root has no parent

            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE;
            var raw_idx: [INDEX_SIZE]u8 = undefined;
            @memcpy(raw_idx[0..], self.raw[offset .. offset + INDEX_SIZE]);
            return std.mem.bytesToValue(usize, &raw_idx);
        }

        /// Retrieves the index of the child node in the specified dir
        /// (either left or right) of the node at index idx in the tree
        fn get_child(self: *const Self, idx: usize, dir: Dir) usize {
            return switch (dir) {
                .Left => get_lchild(self, idx),
                .Right => get_rchild(self, idx),
            };
        }

        /// Retrieves the index of the child node in the opposite direction of the
        /// specified dir (either left or right) of the node at index idx in the tree
        fn get_other_child(self: *const Self, idx: usize, dir: Dir) usize {
            return switch (dir) {
                .Left => get_rchild(self, idx),
                .Right => get_lchild(self, idx),
            };
        }

        /// Retrieves the index of the left child node of the node at index
        /// idx in the tree
        fn get_lchild(self: *const Self, idx: usize) usize {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE;
            var raw_idx: [INDEX_SIZE]u8 = undefined;
            @memcpy(raw_idx[0..], self.raw[offset .. offset + INDEX_SIZE]);
            return std.mem.bytesToValue(usize, &raw_idx);
        }

        /// Retrieves the index of the right child node of the node at index idx
        /// in the tree
        fn get_rchild(self: *const Self, idx: usize) usize {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE * 2;
            var raw_idx: [INDEX_SIZE]u8 = undefined;
            @memcpy(raw_idx[0..], self.raw[offset .. offset + INDEX_SIZE]);
            return std.mem.bytesToValue(usize, &raw_idx);
        }

        fn set_parent(self: *Self, idx: usize, p: usize) void {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&p));
        }

        fn set_color(self: *Self, idx: usize, color: Color) void {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + COLOR_SIZE], std.mem.asBytes(&color));
        }

        fn set_lchild(self: *Self, idx: usize, lc: usize) void {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&lc));
        }

        fn set_rchild(self: *Self, idx: usize, rc: usize) void {
            var offset = NODE_SIZE * idx;
            offset += KEY_SIZE + VALUE_SIZE + COLOR_SIZE + INDEX_SIZE * 2;
            std.mem.copy(u8, self.raw[offset .. offset + INDEX_SIZE], std.mem.asBytes(&rc));
        }

        fn set_key(self: *Self, idx: usize, key: K) void {
            var offset = NODE_SIZE * idx;
            std.mem.copy(u8, self.raw[offset .. offset + KEY_SIZE], std.mem.asBytes(&key));
        }

        pub fn set_value(self: *Self, idx: usize, value: V) void {
            var offset = NODE_SIZE * idx + KEY_SIZE;
            std.mem.copy(u8, self.raw[offset .. offset + VALUE_SIZE], std.mem.asBytes(&value));
        }

        /// The swap function swaps the positions of two nodes in the RBTree
        fn swap(self: *Self, x: usize, y: usize) void {
            var offset1 = NODE_SIZE * x;
            var offset2 = NODE_SIZE * y;
            var buffer: [NODE_SIZE]u8 = undefined;
            @memcpy(buffer[0..], self.raw[offset1 .. offset1 + NODE_SIZE]);

            const lchild_x = self.get_lchild(x);
            const rchild_x = self.get_rchild(x);

            const lchild_y = self.get_lchild(y);
            const rchild_y = self.get_rchild(y);

            if (self.get_parent(x)) |p| {
                if (self.get_lchild(p) == x) {
                    self.set_lchild(p, y);
                } else {
                    self.set_rchild(p, y);
                }
            }
            if (lchild_x != 0) self.set_parent(lchild_x, y);
            if (rchild_x != 0) self.set_parent(rchild_x, y);

            if (self.get_parent(y)) |p| {
                if (self.get_lchild(p) == y) {
                    self.set_lchild(p, x);
                } else {
                    self.set_rchild(p, x);
                }
            }
            if (lchild_y != 0) self.set_parent(lchild_y, x);
            if (rchild_y != 0) self.set_parent(rchild_y, x);

            @memcpy(self.raw[offset1 .. offset1 + NODE_SIZE], self.raw[offset2 .. offset2 + NODE_SIZE]);
            @memcpy(self.raw[offset2 .. offset2 + NODE_SIZE], buffer[0..]);
        }

        /// Walks right until it reaches the last non-leaf node and returns it
        fn max_node(self: *Self, n: usize) usize {
            var ret: usize = n;
            var next: usize = self.get_rchild(ret);
            while (true) {
                if (next == 0) break;
                ret = next;
                next = self.get_rchild(ret);
            }
            return ret;
        }

        /// Add a node at the specified index to linear memory
        fn add(
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

        fn delete_node(self: *Self, x: usize) void {
            if (x >= MAX) return;
            const y = self.count - 1;

            var offset1 = NODE_SIZE * x;
            var offset2 = NODE_SIZE * y;

            if (self.get_parent(y)) |p| {
                if (self.get_lchild(p) == y) {
                    self.set_lchild(p, x);
                } else {
                    self.set_rchild(p, x);
                }
            }

            const lchild = self.get_lchild(y);
            const rchild = self.get_rchild(y);

            if (lchild != 0) self.set_parent(lchild, x);
            if (rchild != 0) self.set_parent(rchild, x);

            @memcpy(self.raw[offset1 .. offset1 + NODE_SIZE], self.raw[offset2 .. offset2 + NODE_SIZE]);
            @memset(self.raw[offset2 .. offset2 + NODE_SIZE], 0);
            self.count -= 1;
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

            if (self.get_rchild(node) != 0) {
                self.print_tree_helper(self.get_rchild(node), indent + INDENT_STEP);
            }

            var i: isize = 0;
            while (i < indent) : (i += 1) {
                std.debug.print(" ", .{});
            }
            if (self.get_color(node) == .Black) {
                std.debug.print("{any}\n", .{self.get_key(node)});
            } else {
                std.debug.print("<{any}>\n", .{self.get_key(node)});
            }

            if (self.get_lchild(node) != 0) {
                self.print_tree_helper(self.get_lchild(node), indent + INDENT_STEP);
            }
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
    try std.testing.expectEqual(tree.get_parent(0), null);
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
    try testing.expectEqual(@intCast(usize, 0), tree.get_parent(4).?);
    try testing.expectEqual(@intCast(u32, 15), tree.get_key(tree.get_rchild(4)));
    try testing.expectEqual(@intCast(usize, 4), tree.get_parent(2).?);
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(2));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(2));
}

test "Get node index" {
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
    //                3  7 nil nil
    tree.add(0, 10, 100, Color.Black, 0, 1, 2); // root node
    tree.add(1, 5, 50, Color.Red, 0, 3, 4);
    tree.add(2, 15, 150, Color.Red, 0, 0, 0);
    tree.add(3, 3, 30, Color.Black, 1, 0, 0);
    tree.add(4, 7, 70, Color.Black, 2, 0, 0);
    tree.count = 5;

    // Find nodes in tree
    try testing.expectEqual(@intCast(usize, 0), tree.get(10).?);
    try testing.expectEqual(@intCast(usize, 1), tree.get(5).?);
    try testing.expectEqual(@intCast(usize, 2), tree.get(15).?);
    try testing.expectEqual(@intCast(usize, 3), tree.get(3).?);
    try testing.expectEqual(@intCast(usize, 4), tree.get(7).?);
}

test "Insert nodes" {
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
    const K = u32;
    const V = u32;
    const MaxNodes = 10;
    const Tree = RBTree(K, V, MaxNodes, S.cmp);
    var tree = Tree{};

    // Initially the tree is empty
    tree.insert(10, 100);
    try testing.expectEqual(@intCast(usize, 0), tree.get(10).?);
    try testing.expectEqual(@intCast(u32, 100), tree.get_value(0));
    try testing.expectEqual(Color.Red, tree.get_color(0));

    tree.insert(5, 50);
    try testing.expectEqual(@intCast(usize, 1), tree.get(5).?);
    try testing.expectEqual(@intCast(u32, 50), tree.get_value(tree.get_lchild(0)));
    try testing.expectEqual(Color.Black, tree.get_color(0));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_lchild(0)));

    tree.insert(15, 150);
    try testing.expectEqual(@intCast(usize, 2), tree.get(15).?);
    try testing.expectEqual(@intCast(u32, 150), tree.get_value(tree.get_rchild(0)));
    try testing.expectEqual(Color.Black, tree.get_color(0));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_lchild(0)));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_rchild(0)));

    tree.insert(3, 30);
    try testing.expectEqual(@intCast(usize, 3), tree.get(3).?);
    try testing.expectEqual(@intCast(u32, 30), tree.get_value(tree.get_lchild(tree.get_lchild(0))));
    try testing.expectEqual(Color.Red, tree.get_color(0));
    try testing.expectEqual(Color.Black, tree.get_color(tree.get_lchild(0)));
    try testing.expectEqual(Color.Black, tree.get_color(tree.get_rchild(0)));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_lchild(tree.get_lchild(0))));

    tree.insert(7, 70);
    try testing.expectEqual(@intCast(usize, 4), tree.get(7).?);
    try testing.expectEqual(@intCast(u32, 70), tree.get_value(tree.get_rchild(tree.get_lchild(0))));
    try testing.expectEqual(Color.Red, tree.get_color(0));
    try testing.expectEqual(Color.Black, tree.get_color(tree.get_lchild(0)));
    try testing.expectEqual(Color.Black, tree.get_color(tree.get_rchild(0)));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_lchild(tree.get_lchild(0))));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_rchild(tree.get_lchild(0))));

    tree.insert(11, 110);
    tree.insert(8, 80);
    try testing.expectEqual(Color.Black, tree.get_color(0));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_lchild(0)));
    try testing.expectEqual(Color.Black, tree.get_color(tree.get_rchild(0)));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_lchild(tree.get_rchild(0))));
    try testing.expectEqual(Color.Black, tree.get_color(tree.get_rchild(tree.get_lchild(0))));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_rchild(tree.get_rchild(tree.get_lchild(0)))));

    tree.insert(12, 120); // this will lead to a rotation of the right side of the tree
    try testing.expectEqual(Color.Black, tree.get_color(0));
    try testing.expectEqual(@intCast(u32, 100), tree.get_value(0));
    try testing.expectEqual(Color.Black, tree.get_color(tree.get_rchild(0)));
    try testing.expectEqual(@intCast(u32, 120), tree.get_value(tree.get_rchild(0)));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_lchild(tree.get_rchild(0))));
    try testing.expectEqual(@intCast(u32, 110), tree.get_value(tree.get_lchild(tree.get_rchild(0))));
    try testing.expectEqual(Color.Red, tree.get_color(tree.get_rchild(tree.get_rchild(0))));
    try testing.expectEqual(@intCast(u32, 150), tree.get_value(tree.get_rchild(tree.get_rchild(0))));
}

test "delete nodes" {
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
    const K = u32;
    const V = u32;
    const MaxNodes = 10;
    const Tree = RBTree(K, V, MaxNodes, S.cmp);
    var tree = Tree{};

    // Initially the tree is empty
    tree.insert(10, 100);
    tree.insert(5, 50);
    tree.insert(15, 150);
    tree.insert(3, 30);
    tree.insert(7, 70);
    tree.insert(11, 110);
    tree.insert(8, 80);
    tree.insert(12, 120);

    // Delete node with key 7
    tree.delete(7);

    var k8 = tree.get(8).?;
    try testing.expectEqual(Color.Red, tree.get_color(k8));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k8));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k8));
    try testing.expectEqual(@intCast(u32, 5), tree.get_key(tree.get_parent(k8).?));

    var k3 = tree.get(3).?;
    try testing.expectEqual(Color.Red, tree.get_color(k3));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k3));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k3));
    try testing.expectEqual(@intCast(u32, 5), tree.get_key(tree.get_parent(k3).?));

    var k5 = tree.get(5).?;
    try testing.expectEqual(Color.Black, tree.get_color(k5));
    try testing.expectEqual(k3, tree.get_lchild(k5));
    try testing.expectEqual(k8, tree.get_rchild(k5));
    try testing.expectEqual(@intCast(u32, 10), tree.get_key(tree.get_parent(k5).?));

    var k11 = tree.get(11).?;
    try testing.expectEqual(Color.Red, tree.get_color(k11));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k11));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k11));
    try testing.expectEqual(@intCast(u32, 12), tree.get_key(tree.get_parent(k11).?));

    var k15 = tree.get(15).?;
    try testing.expectEqual(Color.Red, tree.get_color(k15));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k15));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k15));
    try testing.expectEqual(@intCast(u32, 12), tree.get_key(tree.get_parent(k15).?));

    var k12 = tree.get(12).?;
    try testing.expectEqual(Color.Black, tree.get_color(k12));
    try testing.expectEqual(k11, tree.get_lchild(k12));
    try testing.expectEqual(k15, tree.get_rchild(k12));
    try testing.expectEqual(@intCast(u32, 10), tree.get_key(tree.get_parent(k12).?));

    var k10 = tree.get(10).?;
    try testing.expectEqual(Color.Black, tree.get_color(k10));
    try testing.expectEqual(k5, tree.get_lchild(k10));
    try testing.expectEqual(k12, tree.get_rchild(k10));
    try testing.expectEqual(tree.get_parent(k10), null);

    // Delete node with key 5
    tree.delete(5);

    k8 = tree.get(8).?; // Three moves one up
    try testing.expectEqual(Color.Red, tree.get_color(k8));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k8));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k8));
    try testing.expectEqual(@intCast(u32, 3), tree.get_key(tree.get_parent(k8).?));

    k3 = tree.get(3).?; // Three moves one up
    try testing.expectEqual(Color.Black, tree.get_color(k3));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k3));
    try testing.expectEqual(k8, tree.get_rchild(k3));
    try testing.expectEqual(@intCast(u32, 10), tree.get_key(tree.get_parent(k3).?));

    k11 = tree.get(11).?;
    try testing.expectEqual(Color.Red, tree.get_color(k11));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k11));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k11));
    try testing.expectEqual(@intCast(u32, 12), tree.get_key(tree.get_parent(k11).?));

    k15 = tree.get(15).?;
    try testing.expectEqual(Color.Red, tree.get_color(k15));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k15));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k15));
    try testing.expectEqual(@intCast(u32, 12), tree.get_key(tree.get_parent(k15).?));

    k12 = tree.get(12).?;
    try testing.expectEqual(Color.Black, tree.get_color(k12));
    try testing.expectEqual(k11, tree.get_lchild(k12));
    try testing.expectEqual(k15, tree.get_rchild(k12));
    try testing.expectEqual(@intCast(u32, 10), tree.get_key(tree.get_parent(k12).?));

    k10 = tree.get(10).?;
    try testing.expectEqual(Color.Black, tree.get_color(k10));
    try testing.expectEqual(k5, tree.get_lchild(k10));
    try testing.expectEqual(k12, tree.get_rchild(k10));
    try testing.expectEqual(tree.get_parent(k10), null);

    // Delete root node
    tree.delete(10);

    k11 = tree.get(11).?;
    try testing.expectEqual(Color.Red, tree.get_color(k11));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k11));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k11));
    try testing.expectEqual(@intCast(u32, 12), tree.get_key(tree.get_parent(k11).?));

    k15 = tree.get(15).?;
    try testing.expectEqual(Color.Red, tree.get_color(k15));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k15));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k15));
    try testing.expectEqual(@intCast(u32, 12), tree.get_key(tree.get_parent(k15).?));

    k12 = tree.get(12).?;
    try testing.expectEqual(Color.Black, tree.get_color(k12));
    try testing.expectEqual(k11, tree.get_lchild(k12));
    try testing.expectEqual(k15, tree.get_rchild(k12));
    try testing.expectEqual(@intCast(u32, 8), tree.get_key(tree.get_parent(k12).?));

    tree.delete(8);

    k11 = tree.get(11).?;
    try testing.expectEqual(Color.Red, tree.get_color(k11));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k11));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k11));
    try testing.expectEqual(@intCast(u32, 3), tree.get_key(tree.get_parent(k11).?));

    k3 = tree.get(3).?;
    try testing.expectEqual(Color.Black, tree.get_color(k3));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k3));
    try testing.expectEqual(k11, tree.get_rchild(k3));
    try testing.expectEqual(@intCast(u32, 12), tree.get_key(tree.get_parent(k3).?));

    k15 = tree.get(15).?;
    try testing.expectEqual(Color.Black, tree.get_color(k15));
    try testing.expectEqual(@intCast(usize, 0), tree.get_lchild(k15));
    try testing.expectEqual(@intCast(usize, 0), tree.get_rchild(k15));
    try testing.expectEqual(@intCast(u32, 12), tree.get_key(tree.get_parent(k15).?));

    k12 = tree.get(12).?;
    try testing.expectEqual(Color.Black, tree.get_color(k12));
    try testing.expectEqual(k3, tree.get_lchild(k12));
    try testing.expectEqual(k15, tree.get_rchild(k12));
    try testing.expectEqual(tree.get_parent(k12), null);

    tree.delete(3);
}
