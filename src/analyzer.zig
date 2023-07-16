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

pub fn analyze(self: *Self, comptime ClauseRef: type, context: anytype, cref: ClauseRef) ![]const Lit {
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

            if (!self.int_map.inMap(lit.variable()) and context.levelOf(lit.variable()) > 0) {
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

        while (!self.int_map.inMap(context.assignation_queue.items[index].variable())) : (index -= 1) {}
        pivot = context.assignation_queue.items[index];
        clause = context.reasonOf(pivot.?.variable());
        self.int_map.remove(pivot.?.variable());
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
            if (!self.int_map.inMap(l.variable())) {
                index += 1;
                continue :minimize_loop;
            }
        }

        _ = self.result.swapRemove(index);
    }

    return self.result.items;
}

pub fn analyzeFinal(self: *Self, comptime ClauseRef: type, context: anytype, lit: Lit) ![]const Lit {
    _ = ClauseRef;
    self.clear();

    try self.result.append(lit);

    if (context.level == 0) {
        return self.result.items;
    }

    try self.int_map.insert(lit.variable(), true);

    var index = context.assignation_queue.items.len - 1;

    while (true) : (index -= 1) {
        var l = context.assignation_queue.items[index];
        var v = l.variable();

        if (context.levelOf(v) == 0)
            break;

        if (self.int_map.inMap(v)) {
            if (context.reasonOf(v)) |cref| {
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
