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

const Self = @This();

pub fn init(allocator: std.mem.Allocator) Self {
    var self: Self = undefined;
    self.activity = std.ArrayList(f64).init(allocator);
    self.polarity = std.ArrayList(bool).init(allocator);
    self.heap = Heap(Variable, variableToUsize).init(allocator);
    self.act_increment = 1.0;
    self.act_decay = 0.8;
    return self;
}

pub fn deinit(self: *Self) void {
    self.heap.deinit();
    self.activity.deinit();
    self.polarity.deinit();
}

pub fn addVariable(self: *Self) !void {
    var v = @truncate(Variable, self.activity.items.len);
    try self.heap.insert(v, 0.0);
    try self.polarity.append(true);
    try self.activity.append(0.0);
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
        for (self.activity.items) |*a, i| {
            if (self.heap.inHeap(@truncate(Variable, i)))
                try self.heap.insert(@truncate(Variable, i), -a.* * 1e-100);
            a.* *= 1e-100;
        }
        self.act_increment *= 1e-100;
    }
}

pub fn decayActivity(self: *Self) void {
    self.act_increment *= 1.0 / self.act_decay;
}