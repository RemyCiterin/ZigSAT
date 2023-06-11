const std = @import("std");

// `T` is a type of integer
// `toUsize` is a function to convert a `T` term into an usize
pub fn Heap(comptime T: type, comptime toUsize: anytype) type {
    return struct {
        heap: std.ArrayList(T),
        values: std.ArrayList(f64),
        heap_inv: std.ArrayList(?usize),

        const Self = @This();

        pub fn len(self: Self) usize {
            return self.heap.items.len;
        }

        pub fn clear(self: *Self) void {
            self.heap.clearAndFree();
            self.values.clearAndFree();

            var i: usize = 0;
            while (i < self.heap_inv.items.len) : (i += 1) {
                self.heap_inv.items[i] = null;
            }
        }

        fn swap(self: *Self, i: usize, j: usize) void {
            const v = self.values.items[i];
            self.values.items[i] = self.values.items[j];
            self.values.items[j] = v;

            const x = self.heap.items[i];
            self.heap.items[i] = self.heap.items[j];
            self.heap.items[j] = x;

            self.heap_inv.items[toUsize(self.heap.items[i])] = i;
            self.heap_inv.items[toUsize(self.heap.items[j])] = j;
        }

        pub fn empty(self: Self) bool {
            return self.len() == 0;
        }

        pub fn init(allocator: std.mem.Allocator) Self {
            var heap = std.ArrayList(T).init(allocator);
            var values = std.ArrayList(f64).init(allocator);
            var heap_inv = std.ArrayList(?usize).init(allocator);
            return .{ .heap = heap, .heap_inv = heap_inv, .values = values };
        }

        pub fn deinit(self: *Self) void {
            self.values.deinit();
            self.heap_inv.deinit();
            self.heap.deinit();
        }

        pub fn inHeap(self: Self, x: T) bool {
            return toUsize(x) < self.heap_inv.items.len and
                self.heap_inv.items[toUsize(x)] != null;
        }

        fn parent(i: usize) usize {
            return (i - 1) >> 1;
        }

        fn propagateUp(self: *Self, i: usize) void {
            if (i > 0) {
                var v0 = self.values.items[i];
                var v1 = self.values.items[Self.parent(i)];

                if (v0 < v1) {
                    self.swap(i, Self.parent(i));
                    self.propagateUp(Self.parent(i));
                }
            }
        }

        fn left(i: usize) usize {
            return (i << 1) + 1;
        }
        fn right(i: usize) usize {
            return (i << 1) + 2;
        }

        pub fn getMin(self: Self) T {
            return self.heap.items[0];
        }

        pub fn getMinValue(self: Self) f64 {
            return self.values.items[0];
        }

        pub fn getValue(self: Self, x: T) ?f64 {
            if (self.inHeap(x)) {
                return self.values.items[self.heap_inv.items[toUsize(x)] orelse unreachable];
            } else {
                return null;
            }
        }

        pub fn remove(self: *Self, x: T) void {
            if (self.inHeap(x)) {
                var heap_inv = self.heap_inv.items[toUsize(x)] orelse unreachable;
                self.swap(heap_inv, self.heap.items.len - 1);
                self.heap_inv.items[toUsize(x)] = null;
                _ = self.values.pop();
                _ = self.heap.pop();

                if (heap_inv != self.heap.items.len) {
                    self.propagateDown(heap_inv);
                    self.propagateUp(heap_inv);
                }
            }
        }

        fn propagateDown(self: *Self, heap_inv: usize) void {
            var x = self.heap.items[heap_inv];
            var v = self.values.items[heap_inv];
            var i = heap_inv;

            while (Self.left(i) < self.heap.items.len) {
                var child: usize = undefined;

                if (Self.right(i) < self.heap.items.len and
                    self.values.items[Self.right(i)] < self.values.items[Self.left(i)])
                {
                    child = Self.right(i);
                } else {
                    child = Self.left(i);
                }

                if (self.values.items[child] >= v) {
                    break;
                }

                self.heap.items[i] = self.heap.items[child];
                self.values.items[i] = self.values.items[child];
                self.heap_inv.items[toUsize(self.heap.items[child])] = i;
                i = child;
            }

            self.heap.items[i] = x;
            self.values.items[i] = v;
            self.heap_inv.items[toUsize(x)] = i;
        }

        fn down(self: *Self, x: T) void {
            self.propagateDown(self.heap_inv.items[toUsize(x)] orelse unreachable);
        }

        fn up(self: *Self, x: T) void {
            self.propagateUp(self.heap_inv.items[toUsize(x)] orelse unreachable);
        }

        pub fn insert(self: *Self, x: T, v: f64) !void {
            if (self.inHeap(x)) {
                self.values.items[self.heap_inv.items[toUsize(x)] orelse unreachable] = v;
                self.down(x);
                self.up(x);
            } else {
                try self.insertNew(x, v);
            }
        }

        // assume !self.inHeap(x)
        fn insertNew(self: *Self, x: T, v: f64) !void {
            while (toUsize(x) >= self.heap_inv.items.len) {
                try self.heap_inv.append(null);
            }

            self.heap_inv.items[toUsize(x)] = self.heap.items.len;
            try self.heap.append(x);
            try self.values.append(v);

            self.up(x);
        }
    };
}

pub fn usizeToUsize(x: usize) usize {
    return x;
}

pub fn u32ToUsize(x: u32) usize {
    return @as(usize, x);
}

test "random heap test: test all interface functions" {
    var rnd = std.rand.DefaultPrng.init(0);
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        _ = gpa.deinit();
    }

    comptime var step = 0;
    inline while (step < 100) : (step += 1) {
        var heap = Heap(u32, u32ToUsize).init(allocator);
        defer heap.deinit();

        var i: usize = 0;
        while (i < 200) : (i += 1) {
            var x = rnd.random().int(u32) % 1000;
            var v = rnd.random().float(f64);

            try heap.insert(x, v);
        }

        var val = heap.getMinValue();
        while (heap.len() > 100) {
            try std.testing.expect(val <= heap.getMinValue());

            val = heap.getMinValue();
            heap.remove(heap.getMin());
        }

        heap.clear();
        try std.testing.expect(heap.empty());
    }
}
