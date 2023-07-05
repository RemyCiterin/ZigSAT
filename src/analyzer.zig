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

    context.proof_manager.setBase(cref.proof);

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

        try context.proof_manager.pushStep(pivot.?.variable(), clause.?.proof);
    }

    //const sortFn = struct {
    //    fn lessThan(ctx: @TypeOf(context), l1: Lit, l2: Lit) bool {
    //        return ctx.positionOf(l1.variable()) < ctx.positionOf(l2.variable());
    //    }
    //};

    //std.sort.sort(Lit, self.result.items[1..], context, sortFn.lessThan);

    //var seen: usize = self.result.items.len - 1;

    //minimize_loop: while (seen > 0) {
    //    while (!self.int_map.inMap(context.assignation_queue.items[index].variable())) : (index -= 1) {}
    //    seen -= 1;

    //    var lit = context.assignation_queue.items[index];

    //    if (!self.int_map.get(lit.variable())) {
    //        index -= 1;
    //        continue;
    //    }

    //    var reason = context.reasonOf(lit.variable()) orelse {
    //        index -= 1;
    //        continue;
    //    };

    //    for (reason.expr) |l| {
    //        if (!self.int_map.inMap(l.variable())) {
    //            index -= 1;
    //            continue :minimize_loop;
    //        }
    //    }

    //    try self.int_map.insert(lit.variable(), false);
    //    try context.proof_manager.pushStep(lit.variable(), reason.proof);
    //}

    //index = 1;
    //while (index < self.result.items.len) {
    //    if (!self.int_map.get(self.result.items[index].variable())) {
    //        _ = self.result.swapRemove(index);
    //    } else {
    //        index += 1;
    //    }
    //}

    if (context.gen_proof) {
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
    }

    return self.result.items;
}
