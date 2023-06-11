const std = @import("std");

pub fn IntMap(comptime T: type, comptime V: type, comptime to_usize: anytype) type {
    return struct {
        queue: std.ArrayList(T),
        queue_inverse: std.ArrayList(?usize),
        values: std.ArrayList(?V),

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            var queue_inverse = std.ArrayList(?usize).init(allocator);
            var values = std.ArrayList(?V).init(allocator);
            var queue = std.ArrayList(T).init(allocator);

            return .{ .queue_inverse = queue_inverse, .values = values, .queue = queue };
        }

        pub fn deinit(self: *Self) void {
            self.queue_inverse.deinit();
            self.values.deinit();
            self.queue.deinit();
        }

        pub fn len(self: Self) usize {
            return self.queue.items.len;
        }

        pub fn get(self: Self, x: T) V {
            return self.values.items[to_usize(x)] orelse unreachable;
        }

        pub fn getMut(self: *Self, x: T) *V {
            return &(self.values.items[to_usize(x)] orelse unreachable);
        }

        fn swap(self: *Self, x: usize, y: usize) void {
            var qx = self.queue.items[x];
            self.queue.items[x] = self.queue.items[y];
            self.queue.items[y] = qx;

            self.queue_inverse.items[to_usize(self.queue.items[x])] = x;
            self.queue_inverse.items[to_usize(self.queue.items[y])] = y;
        }

        pub fn inMap(self: Self, x: T) bool {
            return to_usize(x) < self.queue_inverse.items.len and
                self.queue_inverse.items[to_usize(x)] != null;
        }

        pub fn insert(self: *Self, x: T, v: V) !void {
            if (self.inMap(x)) return;

            while (self.queue_inverse.items.len <= to_usize(x)) {
                try self.queue_inverse.append(null);
                try self.values.append(null);
            }

            self.queue_inverse.items[to_usize(x)] = self.queue.items.len;
            try self.queue.append(x);
            self.values.items[to_usize(x)] = v;
        }

        pub fn remove(self: *Self, x: T) void {
            if (!self.inMap(x)) return;

            var end = self.queue.items.len - 1;
            self.swap(end, self.queue_inverse.items[to_usize(x)] orelse unreachable);
            self.queue_inverse.items[to_usize(x)] = null;
            self.values.items[to_usize(x)] = null;
            _ = self.queue.pop();
        }

        pub fn clear(self: *Self) void {
            while (self.queue.items.len > 0) {
                self.queue_inverse.items[self.queue.items.len - 1] = null;
                self.values.items[self.queue.items.len - 1] = null;
                _ = self.queue.pop();
            }
        }
    };
}

test "random int_map test: test all interface functions" {
    var rnd = std.rand.DefaultPrng.init(0);
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        _ = gpa.deinit();
    }

    comptime var step = 0;
    inline while (step < 100) : (step += 1) {
        var int_map = IntMap(u32, u32, @import("Heap.zig").u32ToUsize).init(allocator);
        defer int_map.deinit();

        var i: usize = 0;
        while (i < 200) : (i += 1) {
            var x = rnd.random().int(u32) % 1000;
            var v = rnd.random().int(u32) % 1000;
            try int_map.insert(x, v);
        }

        while (i > 100) : (i -= 1) {
            var x = rnd.random().int(u32) % 1000;
            if (int_map.inMap(x)) {
                int_map.getMut(x).* = 42;
                try std.testing.expect(int_map.get(x) == 42);
                int_map.remove(x);
            }
        }

        int_map.clear();
    }
}
