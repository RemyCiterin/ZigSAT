const std = @import("std");
const IntMap = @import("IntMap.zig").IntMap;
const lbool = @import("lit.zig").lbool;
const Lit = @import("lit.zig").Lit;

const Variable = @import("lit.zig").Variable;
pub const variableToUsize = @import("lit.zig").variableToUsize;

int_map: IntMap(Variable, bool, variableToUsize),

result: std.ArrayList(Lit),

const Self = @This();

pub fn init(allocator: std.mem.Allocator) Self {
    var self: Self = undefined;

    self.int_map = IntMap(Variable, bool, variableToUsize).init(allocator);
    self.result = std.ArrayList(Lit).init(allocator);

    return self;
}

pub fn clear(self: *Self) void {
    self.result.clearRetainingCapacity();
    self.int_map.clear();
}

pub fn deinit(self: *Self) void {
    self.result.deinit();
    self.int_map.deinit();
}

pub fn analyze(self: *Self, comptime Context: type, context: *Context, cref: Context.ClauseRef) ![]const Lit {
    self.clear();

    context.proof_manager.setBase(cref.proof);

    for (cref.expr) |lit|
        try std.testing.expect(context.value(lit) == .lfalse);

    try self.result.append(Lit.init(0, true));

    var IP_counter: usize = 0; // number of implication points of the current clause
    var index = context.assignation_queue.items.len - 1;
    var clause: ?Context.ClauseRef = cref;
    var pivot: ?Lit = null;

    while (true) {
        context.clause_manager.incrActivity(clause.?);

        switch (clause.?.stats) {
            .Learned => |*lcs| {
                var lbd = try context.lbd_stats.getLBD(context, cref.expr);
                if (lbd < lcs.lbd) lcs.lbd = lbd;
            },
            else => {},
        }

        for (clause.?.expr) |lit| {
            if (pivot != null and pivot.?.equals(lit)) continue;

            if (!self.int_map.contain(lit.variable()) and context.levelOf(lit.variable()) > 0) {
                try context.vsids.incrActivity(lit.variable());

                if (context.levelOf(lit.variable()) < context.level) {
                    try self.int_map.insert(lit.variable(), true);
                    try self.result.append(lit);
                } else {
                    try self.int_map.insert(lit.variable(), false);
                    IP_counter += 1;
                }
            }
        }

        while (!self.int_map.contain(context.assignation_queue.items[index].variable())) : (index -= 1) {}
        pivot = context.assignation_queue.items[index];
        clause = context.reasonOf(pivot.?.variable());
        self.int_map.remove(pivot.?.variable());
        self.result.items[0] = pivot.?.not();
        IP_counter -= 1;

        if (IP_counter == 0) break;

        try context.proof_manager.pushStep(pivot.?.variable(), clause.?.proof);
    }

    if (Context.Proof == void) {
        // no proof generation
        index = 1;
        minimize_loop: while (index < self.result.items.len) {
            var v = self.result.items[index].variable();

            var reason = context.reasonOf(v) orelse {
                index += 1;
                continue;
            };

            for (reason.expr) |l| {
                if (!self.int_map.contain(l.variable())) {
                    index += 1;
                    continue :minimize_loop;
                }
            }

            _ = self.result.swapRemove(index);
        }
    }

    return self.result.items;
}

pub fn analyzeFinal(self: *Self, comptime Context: type, context: *Context, lit: Lit) ![]const Lit {
    self.clear();

    try self.result.append(lit);

    if (context.levelOf(lit.variable()) == 0) {
        context.proof_manager.setBase(context.proofOf(lit.variable()));
        return self.result.items;
    }

    try self.int_map.insert(lit.variable(), true);

    var index = context.assignation_queue.items.len - 1;

    while (true) : (index -= 1) {
        var l = context.assignation_queue.items[index];
        var v = l.variable();

        if (context.levelOf(v) == 0)
            break;

        if (self.int_map.contain(v)) {
            if (context.reasonOf(v)) |cref| {
                try context.proof_manager.pushStep(v, cref.proof);
                for (cref.expr) |x| {
                    if (context.levelOf(x.variable()) > 0)
                        try self.int_map.insert(x.variable(), true);
                }
            } else {
                try self.result.append(l.not());
            }
            self.int_map.remove(v);
        }
        if (index == 0) break;
    }

    return self.result.items;
}

/// remove all the variables of level 0 of a proof
pub fn finalizeProof(self: *Self, comptime Context: type, context: *Context, expr: []const Lit) !void {
    _ = self;
    _ = context;
    _ = expr;
}
