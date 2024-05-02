const std = @import("std");

// main data structure used by the solver
const Heap = @import("Heap.zig").Heap;

const lbool = @import("lit.zig").lbool;
const Lit = @import("lit.zig").Lit;

const Variable = @import("lit.zig").Variable;
const variableToUsize = @import("lit.zig").variableToUsize;

heap: Heap(Variable, variableToUsize),
activity: std.ArrayListUnmanaged(f64) = .{},
polarity: std.ArrayListUnmanaged(bool) = .{},
act_increment: f64,
act_decay: f64,
rnd: std.rand.DefaultPrng,

alpha: f64 = 0.4,
learnt_count: isize = 0,
assigned: std.ArrayListUnmanaged(isize) = .{},
participated: std.ArrayListUnmanaged(isize) = .{},
allocator: std.mem.Allocator,

const Self = @This();

const EMA: bool = false;

pub fn init(allocator: std.mem.Allocator) Self {
    return .{
        .allocator = allocator,
        .heap = Heap(Variable, variableToUsize).init(allocator),
        .rnd = std.rand.DefaultPrng.init(0),
        .act_increment = 1.0,
        .act_decay = 0.85,
    };
}

pub fn deinit(self: *Self) void {
    self.heap.deinit();
    self.activity.deinit(self.allocator);
    self.polarity.deinit(self.allocator);

    self.assigned.deinit(self.allocator);
    self.participated.deinit(self.allocator);
}

pub fn addVariable(self: *Self) !void {
    var v: Variable = @truncate(self.activity.items.len);
    var a: f64 = self.rnd.random().float(f64) * 0.01;
    var p: bool = self.rnd.random().float(f32) > 0.5;
    try self.polarity.append(self.allocator, p);
    try self.activity.append(self.allocator, a);
    try self.heap.insert(v, -a);

    try self.assigned.append(self.allocator, 0);
    try self.participated.append(self.allocator, 0);
}

pub fn setState(self: *Self, v: Variable, st: lbool) !void {
    switch (st) {
        .lundef => {
            var interval = self.learnt_count - self.assigned.items[v];
            if (EMA and interval > 0) {
                var a = self.activity.items[v];
                var i: f64 = @floatFromInt(interval);
                var p: f64 = @floatFromInt(self.participated.items[v]);
                self.activity.items[v] =
                    (1.0 - self.alpha) * a + self.alpha * p / i;
            }

            try std.testing.expect(!self.heap.inHeap(v));
            try self.heap.insert(v, -self.activity.items[v]);
        },
        else => {
            self.participated.items[v] = 0;
            self.assigned.items[v] = self.learnt_count;

            try std.testing.expect(self.heap.inHeap(v));
            self.polarity.items[v] = st.sign();
            self.heap.remove(v);
        },
    }
}

pub fn mkDecision(self: *Self) ?Lit {
    if (self.heap.empty()) return null;

    var v = self.heap.getMin();
    var p = self.polarity.items[v];

    return Lit.init(v, p);
}

pub fn incrActivity(self: *Self, v: Variable) !void {
    if (EMA) {
        self.participated.items[v] += 1;
    } else {
        var act = self.activity.items[v] + self.act_increment;
        self.activity.items[v] = act;

        if (self.heap.inHeap(v))
            try self.heap.insert(v, -act);

        if (act > 1e100) {
            for (self.activity.items, 0..) |*a, i| {
                if (self.heap.inHeap(@truncate(i)))
                    try self.heap.insert(@truncate(i), -a.* * 1e-100);
                a.* *= 1e-100;
            }
            self.act_increment *= 1e-100;
        }
    }
}

pub fn decayActivity(self: *Self) void {
    self.act_increment *= 1.0 / self.act_decay;

    self.learnt_count += 1;
    if (self.alpha > 0.06)
        self.alpha -= 1e-6;
}
