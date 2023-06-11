const std = @import("std");

pub fn IntSet(comptime T: type, comptime to_usize: anytype) type {
    return struct {
        queue: std.ArrayList(T),
        queue_inverse: std.ArrayList(?usize),

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            var queue_inverse = std.ArrayList(?usize).init(allocator);
            var queue = std.ArrayList(T).init(allocator);

            return .{ .queue_inverse = queue_inverse, .queue = queue };
        }

        pub fn iter(self: *Self) []const T {
            return self.queue.items;
        }

        pub fn deinit(self: *Self) void {
            self.queue_inverse.deinit();
            self.queue.deinit();
        }

        pub fn len(self: Self) usize {
            return self.queue.items.len;
        }

        fn swap(self: *Self, x: usize, y: usize) void {
            var qx = self.queue.items[x];
            self.queue.items[x] = self.queue.items[y];
            self.queue.items[y] = qx;

            self.queue_inverse.items[to_usize(self.queue.items[x])] = x;
            self.queue_inverse.items[to_usize(self.queue.items[y])] = y;
        }

        pub fn inSet(self: Self, x: T) bool {
            return to_usize(x) < self.queue_inverse.items.len and
                self.queue_inverse.items[to_usize(x)] != null;
        }

        pub fn insert(self: *Self, x: T) !void {
            if (self.inSet(x)) return;

            while (self.queue_inverse.items.len <= to_usize(x)) {
                try self.queue_inverse.append(null);
            }

            self.queue_inverse.items[to_usize(x)] = self.queue.items.len;
            try self.queue.append(x);
        }

        pub fn remove(self: *Self, x: T) void {
            if (!self.inSet(x)) return;

            var end = self.queue.items.len - 1;
            self.swap(end, self.queue_inverse.items[to_usize(x)] orelse unreachable);
            self.queue_inverse.items[to_usize(x)] = null;
            _ = self.queue.pop();
        }

        pub fn clear(self: *Self) void {
            for (self.queue.items) |x| {
                self.queue_inverse.items[to_usize(x)] = null;
            }
            self.queue.clearRetainingCapacity();
        }
    };
}

test "random int_set test: test all interface functions" {
    var rnd = std.rand.DefaultPrng.init(0);
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        _ = gpa.deinit();
    }

    comptime var step = 0;
    inline while (step < 100) : (step += 1) {
        var int_set = IntSet(u32, @import("Heap.zig").u32ToUsize).init(allocator);
        defer int_set.deinit();

        var i: usize = 0;
        while (i < 200) : (i += 1) {
            var x = rnd.random().int(u32) % 1000;
            try int_set.insert(x);
        }

        while (i > 100) : (i -= 1) {
            var x = rnd.random().int(u32) % 1000;
            if (int_set.inSet(x)) int_set.remove(x);
        }

        int_set.clear();
    }
}
