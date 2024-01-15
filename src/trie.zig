//! this file define a type of trie and some utility to manipulate them

const std = @import("std");
const Allocator = std.mem.Allocator;

pub const Item = u64;
pub const Key = []const Item;

/// a type of (not-empty) trie of a given size
const TrieUnmanaged = struct {
    const Self = TrieUnmanaged;

    /// the subtries of the trie, of size different to `1`, and contain sequences of size
    /// `size - 1 - prefix.items.len`, if it is empty then `size == prefix.items.len`
    children: std.AutoHashMapUnmanaged(Item, Self),

    /// the prefix of all the sequences represented by the trie
    prefix: std.ArrayListUnmanaged(Item),

    /// the size of the sequences represented the trie
    size: usize,

    /// return a trie with an unique sequence
    fn init(allocator: Allocator, key: Key) !Self {
        var prefix = std.ArrayListUnmanaged(Item){};
        try prefix.appendSlice(allocator, key);
        return .{
            .prefix = prefix,
            .size = key.len,
            .children = .{},
        };
    }

    /// free all the interal data structures
    fn deinit(self: *Self, allocator: Allocator) void {
        var iterator = self.children.valueIterator();
        while (iterator.next()) |next| {
            next.deinit(allocator);
        }

        self.children.deinit(allocator);
        self.prefix.deinit(allocator);
    }

    /// return if the trie contain at least one sequence that start by a given prefix
    fn contain(self: Self, prefix: Key) bool {
        var index: usize = 0;
        while (index < self.prefix.items.len) : (index += 1) {
            if (prefix.len <= index) return true;

            if (self.prefix.items[index] != prefix[index])
                return false;
        }

        if (index == prefix.len) return true;

        if (self.children.get(prefix[index])) |next| return next.contain(prefix[index + 1 ..]);
        return false;
    }

    /// insert a sequence in self, return true if the sequence is already present
    fn insert(self: *Self, allocator: Allocator, key: Key) !void {
        try std.testing.expect(key.len == self.size);

        var index: usize = 0;
        while (index < self.prefix.items.len) : (index += 1) {
            if (self.prefix.items[index] != key[index]) {
                var node1 = try Self.init(allocator, key[index + 1 ..]);
                var node2 = try Self.init(allocator, self.prefix.items[index + 1 ..]);

                node2.size = self.size - index - 1;
                node2.children = self.children;

                self.children = .{};
                try self.children.put(allocator, self.prefix.items[index], node2);
                try self.children.put(allocator, key[index], node1);
                try self.prefix.resize(allocator, index);

                return;
            }
        }

        if (index == key.len) {
            try std.testing.expect(self.children.count() == 0);
            return;
        }

        if (self.children.getPtr(key[index])) |next| {
            try next.insert(allocator, key[index + 1 ..]);
            return;
        }

        var next = try Self.init(allocator, key[index + 1 ..]);
        try self.children.put(allocator, key[index], next);
    }

    /// remove all the sub-tries that start by a given prefix, return
    /// `true` if the resulting trie is empty (then we must deinit it)
    fn remove(self: *Self, allocator: Allocator, prefix: Key) !bool {
        var index: usize = 0;
        while (index < self.prefix.items.len) : (index += 1) {
            if (prefix.len <= index) return true;

            if (self.prefix.items[index] != prefix[index])
                return false;
        }

        if (index == prefix.len) return true;

        // `self.children.count() >= 2`
        if (self.children.getPtr(prefix[index])) |next| {
            if (!try next.remove(allocator, prefix[index + 1 ..])) return false;

            // we must delete the branch `key[index]`
            next.deinit(allocator);
            _ = self.children.remove(prefix[index]);

            if (self.children.count() >= 2) return false;

            // in this case `self.children.count() == 1`

            var iterator = self.children.iterator();
            while (iterator.next()) |entry| {
                var c = entry.key_ptr.*;
                var n = entry.value_ptr.*;

                self.children.deinit(allocator);
                self.children = n.children;

                try self.prefix.append(allocator, c);
                try self.prefix.appendSlice(allocator, n.prefix.items);
                return false;
            }

            unreachable;
        }

        return false;
    }

    /// not mutable view of the trie, allow to navigate into a trie
    const ViewUnamaged = struct {
        prefix: Key,

        /// use `*` because `children.iterator` need `*const` and `*const` is not type checked very well,
        /// but `ViewUnamaged` doesn't contain mutable operations
        children: *std.AutoHashMapUnmanaged(Item, Self),
        size: usize,

        const IteratorUnmanaged = union(enum) {
            singleton: Singleton,
            multiple: std.AutoHashMapUnmanaged(Item, Self).Iterator,

            const Singleton = struct { seen: bool = false, item: Item, next: ViewUnamaged };

            const Entry = struct {
                item: Item,
                next: ViewUnamaged,
            };

            fn next(self: *IteratorUnmanaged) ?Entry {
                switch (self.*) {
                    .singleton => |*content| {
                        if (content.seen) return null;
                        content.seen = true;
                        return .{ .item = content.item, .next = content.next };
                    },
                    .multiple => |*content| {
                        var entry = content.next() orelse return null;
                        return .{
                            .item = entry.key_ptr.*,
                            .next = entry.value_ptr.view(),
                        };
                    },
                }
            }
        };

        /// return an iterator over the trie view
        fn iter(self: ViewUnamaged) IteratorUnmanaged {
            if (self.prefix.len > 0) {
                return .{ .singleton = .{
                    .item = self.prefix[0],
                    .next = .{
                        .size = self.size - 1,
                        .prefix = self.prefix[1..],
                        .children = self.children,
                    },
                } };
            }

            return .{ .multiple = self.children.iterator() };
        }

        /// given a view and a sequence, move into the view using a sequence
        fn move(self: ViewUnamaged, seq: Key) ?ViewUnamaged {
            var index: usize = 0;
            while (index < self.prefix.len) : (index += 1) {
                if (seq.len <= index)
                    return .{
                        .prefix = self.prefix[index..],
                        .size = self.size - index,
                        .children = self.children,
                    };

                if (self.prefix[index] != seq[index]) return null;
            }

            if (index == seq.len) return .{
                .prefix = &[0]Item{},
                .size = self.size - index,
                .children = self.children,
            };

            if (self.children.getPtr(seq[index])) |next|
                return next.view().move(seq[index + 1 ..]);

            return null;
        }
    };

    /// return a tmp view other the trie
    fn view(self: *Self) ViewUnamaged {
        return ViewUnamaged{
            .size = self.size,
            .children = &self.children,
            .prefix = self.prefix.items,
        };
    }
};

trie: ?TrieUnmanaged,
allocator: Allocator,
size: usize,

pub fn init(allocator: Allocator, size: usize) @This() {
    return .{ .trie = null, .allocator = allocator, .size = size };
}

pub fn deinit(self: *@This()) void {
    if (self.trie) |*trie| trie.deinit(self.allocator);
}

pub fn contain(self: @This(), prefix: Key) bool {
    if (self.trie) |trie| return trie.contain(prefix);
    return false;
}

pub fn insert(self: *@This(), key: Key) !void {
    try std.testing.expect(key.len == self.size);

    if (self.trie) |*trie| return try trie.insert(self.allocator, key);
    self.trie = try TrieUnmanaged.init(self.allocator, key);
}

pub fn remove(self: *@This(), prefix: Key) !void {
    if (self.trie) |*trie| {
        if (try trie.remove(self.allocator, prefix)) {
            trie.deinit(self.allocator);
            self.trie = null;
        }
    }
}

pub const View = struct {
    view: ?TrieUnmanaged.ViewUnamaged,

    pub const Iterator = struct {
        iterator: ?TrieUnmanaged.ViewUnamaged.IteratorUnmanaged,

        pub const Entry = struct { item: Item, next: View };

        pub fn next(self: *Iterator) ?Entry {
            if (self.iterator) |*iterator| {
                var entry = iterator.next() orelse return null;
                return .{
                    .item = entry.item,
                    .next = View{ .view = entry.next },
                };
            }

            return null;
        }
    };

    pub fn move(self: View, seq: Key) View {
        if (self.view) |v| {
            return .{ .view = v.move(seq) };
        }
        return self;
    }

    pub fn iter(self: View) Iterator {
        if (self.view) |v|
            return .{ .iterator = v.iter() };
        return .{ .iterator = null };
    }
};

pub fn view(self: *@This()) View {
    if (self.trie) |*trie|
        return .{ .view = trie.view() };
    return .{ .view = null };
}

test "trie" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        const deinit_status = gpa.deinit();
        //fail test; can't try in defer as defer is executed after we return
        if (deinit_status == .leak) std.testing.expect(false) catch @panic("TEST FAIL");
    }

    var trie = init(allocator, 4);
    defer trie.deinit();

    try trie.insert(&[_]u64{ 1, 2, 3, 4 });

    try trie.insert(&[_]u64{ 1, 2, 3, 5 });
    try trie.insert(&[_]u64{ 1, 2, 3, 6 });
    try trie.insert(&[_]u64{ 1, 3, 3, 5 });
    try trie.insert(&[_]u64{ 1, 2, 4, 5 });

    try std.testing.expect(trie.contain(&[_]u64{ 1, 2, 3 }));
    try std.testing.expect(trie.contain(&[_]u64{ 1, 2, 3, 4 }));
    try std.testing.expect(trie.contain(&[_]u64{ 1, 2, 3, 5 }));

    //_ = try trie.remove(&[_]u64{ 1, 2, 3, 5 });
    //try std.testing.expect(!trie.contain(&[_]u64{ 1, 2, 3, 5 }));

    try std.testing.expect(trie.contain(&[_]u64{ 1, 2, 3 }));
    try std.testing.expect(trie.contain(&[_]u64{ 1, 2, 3, 4 }));
    try std.testing.expect(trie.contain(&[_]u64{ 1, 3, 3, 5 }));
    try std.testing.expect(trie.contain(&[_]u64{ 1, 2, 4, 5 }));
    try std.testing.expect(trie.contain(&[_]u64{ 1, 2, 3, 6 }));

    var v = trie.view();
    v = v.move(&[_]u64{ 1, 2, 3 });

    var iterator = v.iter();

    std.debug.print("\n", .{});
    while (iterator.next()) |entry| {
        std.debug.print("{}\n", .{entry.item});
    }

    std.debug.print("\n", .{});
}
