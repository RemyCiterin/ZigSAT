const std = @import("std");
const RingBuffer = @import("RingBuffer.zig").RingBuffer;

lt_sum: usize,
st_sum: usize,

lt_cap: usize,
cap: usize,

buffer: RingBuffer(usize),

num_conflicts: usize,
need_conflicts: usize,

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

    self.num_conflicts = 0;
    self.need_conflicts = 100;

    self.assign_cap = 5000;
    self.assign_buffer = try RingBuffer(usize).init(self.assign_cap, allocator);
    self.assign_sum = 0;

    return self;
}

pub fn deinit(self: *Self) void {
    self.assign_buffer.deinit();
    self.buffer.deinit();
}

pub fn clear(self: *Self) void {
    self.buffer.clear();
    self.need_conflicts += 300;
    self.st_sum = 0;
}

pub fn addNumAssign(self: *Self, num_assign: usize) !void {
    try self.assign_buffer.append(num_assign);
    self.assign_sum += num_assign;

    const assign_sum = @intToFloat(f64, self.assign_sum);
    const assign_cap = @intToFloat(f64, self.assign_cap);

    if (self.assign_buffer.full())
        if (@intToFloat(f64, num_assign) > 1.4 * assign_sum / assign_cap)
            return self.clear();
}

pub fn append(self: *Self, lbd: usize, size: usize) !void {
    if (self.buffer.full())
        self.st_sum -= self.buffer.pop() orelse unreachable;

    if (self.assign_buffer.full())
        self.assign_sum -= self.assign_buffer.pop() orelse unreachable;

    try self.buffer.append(lbd);
    self.st_sum += lbd;
    self.lt_sum += lbd;

    self.num_conflicts += 1;

    self.mean_size += 0.01 * (@intToFloat(f64, size) - self.mean_size);
}

pub fn needRestart(self: Self) bool {
    if (!self.buffer.full())
        return false;

    //return self.need_conflicts < self.num_conflicts;

    const st_sum = @intToFloat(f64, self.st_sum);
    const lt_sum = @intToFloat(f64, self.lt_sum);
    const cap = @intToFloat(f64, self.cap);
    const lt_cap = @intToFloat(f64, self.num_conflicts);

    return st_sum * 0.8 / cap > lt_sum / lt_cap;
}
