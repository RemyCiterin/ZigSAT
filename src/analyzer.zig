const std = @import("std");
const IntSet = @import("IntSet.zig").IntSet;
const lbool = @import("lit.zig").lbool;
const Lit = @import("lit.zig").Lit;
const Clause = @import("clause.zig").Clause;
const ClauseRef = @import("clause.zig").ClauseRef;

const Variable = @import("lit.zig").Variable;
pub const variableToUsize = @import("lit.zig").variableToUsize;

int_set: IntSet(Variable, variableToUsize),

result: std.ArrayList(Lit),

const Self = @This();

pub fn init(allocator: std.mem.Allocator) Self {
    var self: Self = undefined;

    self.int_set = IntSet(Variable, variableToUsize).init(allocator);
    self.result = std.ArrayList(Lit).init(allocator);

    return self;
}

pub fn clear(self: *Self) void {
    self.result.clearRetainingCapacity();
    self.int_set.clear();
}

pub fn deinit(self: *Self) void {
    self.result.deinit();
    self.int_set.deinit();
}

pub fn analyze(self: *Self, context: anytype, cref: ClauseRef) ![]const Lit {
    self.clear();

    for (cref.expr) |lit|
        try std.testing.expect(context.value(lit) == .lfalse);

    try self.result.append(Lit.init(0, true));

    var IP_counter: usize = 0; // number of implication points of the current clause
    var index = context.assignation_queue.items.len - 1;
    var clause: ?ClauseRef = cref;
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

            if (!self.int_set.inSet(lit.variable()) and context.levelOf(lit.variable()) > 0) {
                try context.vsids.incrActivity(lit.variable());
                try self.int_set.insert(lit.variable());

                if (context.levelOf(lit.variable()) < context.level) {
                    try self.result.append(lit);
                } else {
                    IP_counter += 1;
                }
            }
        }

        while (!self.int_set.inSet(context.assignation_queue.items[index].variable())) : (index -= 1) {}
        pivot = context.assignation_queue.items[index];
        clause = context.reasonOf(pivot.?.variable());
        self.int_set.remove(pivot.?.variable());
        self.result.items[0] = pivot.?.not();
        IP_counter -= 1;

        if (IP_counter == 0) break;
    }

    index = 1;
    minimize_loop: while (index < self.result.items.len) {
        var v = self.result.items[index].variable();

        var reason = context.reasonOf(v) orelse {
            index += 1;
            continue;
        };

        for (reason.expr) |l| {
            if (!self.int_set.inSet(l.variable())) {
                index += 1;
                continue :minimize_loop;
            }
        }

        _ = self.result.swapRemove(index);
    }

    return self.result.items;
}
