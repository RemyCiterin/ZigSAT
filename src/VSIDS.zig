const std = @import("std");

// main data structure used by the solver
const Heap = @import("Heap.zig").Heap;

const lbool = @import("lit.zig").lbool;
const Lit = @import("lit.zig").Lit;

const Variable = @import("lit.zig").Variable;
const variableToUsize = @import("lit.zig").variableToUsize;

heap: Heap(Variable, variableToUsize),
activity: std.ArrayList(f64),
polarity: std.ArrayList(bool),
act_increment: f64,
act_decay: f64,
rnd: std.rand.DefaultPrng,

const Self = @This();

pub fn init(allocator: std.mem.Allocator) Self {
    var self: Self = undefined;
    self.activity = std.ArrayList(f64).init(allocator);
    self.polarity = std.ArrayList(bool).init(allocator);
    self.heap = Heap(Variable, variableToUsize).init(allocator);
    self.rnd = std.rand.DefaultPrng.init(0);
    self.act_increment = 1.0;
    self.act_decay = 0.85;
    return self;
}

pub fn deinit(self: *Self) void {
    self.heap.deinit();
    self.activity.deinit();
    self.polarity.deinit();
}

pub fn addVariable(self: *Self) !void {
    var v: Variable = @truncate(self.activity.items.len);
    var a: f64 = self.rnd.random().float(f64) * 0.1;
    var p: bool = self.rnd.random().float(f32) > 0.5;
    try self.heap.insert(v, -a);
    try self.polarity.append(p);
    try self.activity.append(a);
}

pub fn setState(self: *Self, v: Variable, st: lbool) !void {
    switch (st) {
        .lundef => {
            try std.testing.expect(!self.heap.inHeap(v));
            try self.heap.insert(v, -self.activity.items[v]);
        },
        else => {
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

pub fn decayActivity(self: *Self) void {
    self.act_increment *= 1.0 / self.act_decay;
}
