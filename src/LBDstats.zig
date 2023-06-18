const std = @import("std");
const RingBuffer = @import("RingBuffer.zig").RingBuffer;
const IntSet = @import("IntSet.zig").IntSet;
const Lit = @import("lit.zig").Lit;

lt_sum: usize,
st_sum: usize,

cap: usize,

buffer: RingBuffer(usize),

int_set: IntSet(u32, @import("Heap.zig").u32ToUsize),

num_conflicts: usize,

mean_size: f64,

assign_cap: usize,
assign_buffer: RingBuffer(usize),
assign_sum: usize,

const Self = @This();

pub fn init(allocator: std.mem.Allocator) !Self {
    var self: Self = undefined;

    self.cap = 50;
    self.buffer = try RingBuffer(usize).init(self.cap, allocator);
    self.lt_sum = 0;
    self.st_sum = 0;

    self.int_set = IntSet(u32, @import("Heap.zig").u32ToUsize).init(allocator);

    self.num_conflicts = 0;
    self.mean_size = 0.0;

    self.assign_cap = 5000;
    self.assign_buffer = try RingBuffer(usize).init(self.assign_cap, allocator);
    self.assign_sum = 0;

    return self;
}

pub fn deinit(self: *Self) void {
    self.int_set.deinit();
    self.assign_buffer.deinit();
    self.buffer.deinit();
}

pub fn clear(self: *Self) void {
    self.buffer.clear();
    self.st_sum = 0;
}

pub fn addNumAssign(self: *Self, num_assign: usize) !void {
    if (self.assign_buffer.full())
        self.assign_sum -= self.assign_buffer.pop() orelse unreachable;

    try self.assign_buffer.append(num_assign);
    self.assign_sum += num_assign;

    const assign_sum = @intToFloat(f64, self.assign_sum);
    const assign_cap = @intToFloat(f64, self.assign_cap);

    if (self.assign_buffer.full())
        if (@intToFloat(f64, num_assign) > 1.4 * assign_sum / assign_cap)
            self.clear();
}

pub fn getLBD(self: *Self, solver: anytype, expr: []const Lit) !usize {
    self.int_set.clear();

    for (expr) |lit| {
        try self.int_set.insert(solver.levelOf(lit.variable()));
    }

    return self.int_set.len();
}

pub fn append(self: *Self, lbd: usize, size: usize) !void {
    if (self.buffer.full())
        self.st_sum -= self.buffer.pop() orelse unreachable;

    try self.buffer.append(lbd);
    self.st_sum += lbd;
    self.lt_sum += lbd;

    self.num_conflicts += 1;

    self.mean_size += 0.01 * (@intToFloat(f64, size) - self.mean_size);
}

pub fn needRestart(self: Self) bool {
    if (!self.buffer.full())
        return false;

    const st_sum = @intToFloat(f64, self.st_sum);
    const lt_sum = @intToFloat(f64, self.lt_sum);
    const cap = @intToFloat(f64, self.cap);
    const lt_cap = @intToFloat(f64, self.num_conflicts);

    return st_sum * 0.8 / cap > lt_sum / lt_cap;
}
