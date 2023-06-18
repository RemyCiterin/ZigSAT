const std = @import("std");

pub fn RingBuffer(comptime T: type) type {
    return struct {
        const Err = error{Full};
        const Self = @This();

        begin: usize = 0,
        end: usize = 0,

        data: []T,

        allocator: std.mem.Allocator,

        pub fn init(cap: usize, allocator: std.mem.Allocator) !Self {
            var data = try allocator.alloc(T, cap);

            return Self{ .data = data, .allocator = allocator, .begin = 0, .end = 0 };
        }

        pub fn deinit(self: *Self) void {
            self.allocator.free(self.data);
        }

        pub fn clear(self: *Self) void {
            self.begin = 0;
            self.end = 0;
        }

        pub fn next(self: Self, index: usize) usize {
            if (1 + index == self.data.len)
                return 0;
            return index + 1;
        }

        pub fn full(self: Self) bool {
            return self.begin == self.next(self.end);
        }

        pub fn empty(self: Self) bool {
            return self.begin == self.end;
        }

        pub fn append(self: *Self, t: T) Err!void {
            if (self.full()) return error.Full;
            self.data[self.end] = t;
            self.end = self.next(self.end);
        }

        pub fn pop(self: *Self) ?T {
            if (self.empty()) return null;
            var t = self.data[self.begin];
            self.begin = self.next(self.begin);
            return t;
        }
    };
}
