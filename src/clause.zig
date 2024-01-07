//! Definition of clause and clause manager (allocator and GC). For the moment the allocator
//! only use reference conting

const std = @import("std");
const Lit = @import("lit.zig").Lit;
const lbool = @import("lit.zig").lbool;

/// statistics of a learned clause
pub const LearnedClauseStats = struct {
    /// activity of a clause, increase at each conflict
    activity: f64 = 0.0,

    /// literal block distance of the clause
    lbd: usize = 0,
};

pub const ClauseStats = union(enum) {
    Learned: LearnedClauseStats,
    Initial,
};

/// clause description
pub fn Clause(comptime P: type) type {
    return struct {
        /// statistics of the clause
        stats: ClauseStats,

        /// a proof of the clause
        proof: P,

        /// expression of the clause, the two firsts literals are named
        /// watched literals, they change with time
        expr: []Lit,

        /// the garbadge collector cannot delete a learned clause if lock is strictly positive
        lock: u32,

        pub fn setLBD(self: *@This(), lbd: usize) void {
            switch (self.stats) {
                .Learned => |*lcs| lcs.lbd = lbd,
                else => {},
            }
        }

        fn setActivity(self: *@This(), act: f64) void {
            switch (self.stats) {
                .Learned => |*lcs| lcs.activity = act,
                else => {},
            }
        }
    };
}

pub fn ClauseDB(comptime P: type) type {
    return struct {
        const DB = @import("db.zig").DB(Clause(P));
        pub const ClauseRef = struct {
            id: DB.Id,
            learned: bool,

            pub fn equal(self: @This(), other: @This()) bool {
                if (self.learned == other.learned)
                    return self.id.equal(other.id);

                return false;
            }
        };

        pub const Iterator = struct {
            learned: bool,
            iter: DB.Iterator,

            pub fn next(self: *@This()) ?ClauseRef {
                var id = self.iter.next() orelse return null;
                return .{ .id = id, .learned = self.learned };
            }
        };

        /// allocator for the diffents arena allocators
        allocator: std.mem.Allocator,

        /// arena allocator
        main_arena: std.heap.ArenaAllocator,

        /// list of used learned clause by the solver
        learned_clauses: DB,

        /// list of initial clause used by the solver
        initial_clauses: DB,

        /// clause activity decay factor
        activity_decay_factor: f64,

        /// current activity add at each call of incrActivity
        activity_increment: f64,

        const Self = @This();

        /// initialize a clause manager
        pub fn init(allocator: std.mem.Allocator) Self {
            return Self{
                .learned_clauses = DB.init(allocator),
                .initial_clauses = DB.init(allocator),
                .main_arena = std.heap.ArenaAllocator.init(allocator),
                .activity_decay_factor = 0.99,
                .activity_increment = 1.0,
                .allocator = allocator,
            };
        }

        /// free it's database but not it's clauses
        pub fn deinit(self: *Self) void {
            var iter = self.initial_clauses.iter();
            while (iter.next()) |id| {
                var c = self.initial_clauses.borrow(id);
                self.allocator.free(c.expr);
            }

            self.initial_clauses.deinit();
            self.learned_clauses.deinit();

            self.main_arena.deinit();
        }

        pub fn borrow(self: *Self, cref: ClauseRef) *Clause(P) {
            if (cref.learned) {
                return self.learned_clauses.borrow(cref.id);
            } else {
                return self.initial_clauses.borrow(cref.id);
            }
        }

        pub fn free(self: *Self, cref: ClauseRef) void {
            if (cref.learned) {
                self.learned_clauses.free(cref.id);
            } else {
                self.initial_clauses.free(cref.id);
            }
        }

        pub fn is_free(self: *Self, cref: ClauseRef) bool {
            if (cref.learned) {
                return self.learned_clauses.is_free(cref.id);
            } else {
                return self.initial_clauses.is_free(cref.id);
            }
        }

        pub fn iter_learned(self: *Self) Iterator {
            return Iterator{ .learned = true, .iter = self.learned_clauses.iter() };
        }

        pub fn iter_initial(self: *Self) Iterator {
            return Iterator{ .learned = false, .iter = self.initial_clauses.iter() };
        }

        pub fn len_learned(self: *Self) usize {
            return self.learned_clauses.len();
        }

        pub fn len_initial(self: *Self) usize {
            return self.initial_clauses.len();
        }

        /// this function clone the expression
        /// the caller have to dealloc it itself
        pub fn initClause(self: *Self, is_learned: bool, expr: []const Lit, proof: P) !ClauseRef {
            var new_expr: []Lit = undefined;
            var cref: ClauseRef = undefined;
            var stats: ClauseStats = undefined;

            if (is_learned) {
                new_expr = try self.main_arena.allocator().alloc(Lit, expr.len);
                cref = ClauseRef{
                    .learned = true,
                    .id = try self.learned_clauses.alloc(undefined),
                };

                var st = LearnedClauseStats{};
                stats = ClauseStats{ .Learned = st };
            } else {
                new_expr = try self.allocator.alloc(Lit, expr.len);
                cref = ClauseRef{
                    .learned = false,
                    .id = try self.initial_clauses.alloc(undefined),
                };

                stats = ClauseStats.Initial;
            }

            std.mem.copy(Lit, new_expr, expr);

            self.borrow(cref).* = .{
                .stats = stats,
                .expr = new_expr,
                .proof = proof,
                .lock = 0,
            };

            return cref;
        }

        pub fn incrActivity(self: *Self, cref: ClauseRef) void {
            var clause: *Clause(P) = self.borrow(cref);
            if (clause.stats == .Initial) return;

            clause.stats.Learned.activity += self.activity_increment;

            if (clause.stats.Learned.activity > 1e20) {
                var learned = self.iter_learned();

                while (learned.next()) |c| {
                    self.borrow(c).stats.Learned.activity *= 1e-20;
                }
                self.activity_increment *= 1e-20;
            }
        }

        pub fn decayActivity(self: *Self) void {
            self.activity_increment *= 1.0 / self.activity_decay_factor;
        }

        pub fn printClause(self: *Self, cref: ClauseRef) void {
            var clause = self.borrow(cref);
            for (clause.expr) |lit| {
                var x: i64 = @intCast(lit.variable());
                var y: i64 = if (lit.sign()) x else -x;
                std.debug.print("{} ", .{y});
            }
            std.debug.print("\n", .{});
        }

        pub fn printDB(self: *Self) void {
            std.debug.print("initial clauses\n", .{});

            for (self.initial_clauses.elems.items) |clause| {
                self.printClause(clause);
            }

            std.debug.print("learned clauses\n", .{});

            for (self.learned_clauses.elems.items) |clause| {
                self.printClause(clause);
            }
        }

        fn clauseLessThan(self: *Self, lhs_ref: ClauseRef, rhs_ref: ClauseRef) bool {
            var lhs = self.borrow(lhs_ref);
            var rhs = self.borrow(rhs_ref);

            if (lhs.stats.Learned.lbd != rhs.stats.Learned.lbd)
                return lhs.stats.Learned.lbd > rhs.stats.Learned.lbd;

            //if (lhs.expr.len != rhs.expr.len)
            //    return lhs.expr.len < rhs.expr.len;

            return lhs.stats.Learned.activity < rhs.stats.Learned.activity;
        }

        /// `fraction` is the fraction of clauses we keep the database
        pub fn garbadgeCollect(self: *Self, fraction: f64) !void {
            var learned_ref = try std.ArrayList(ClauseRef).initCapacity(
                self.allocator,
                self.learned_clauses.len(),
            );
            defer learned_ref.deinit();

            var iter = self.learned_clauses.iter();
            while (iter.next()) |id| {
                try learned_ref.append(.{ .id = id, .learned = true });
            }

            std.mem.sort(ClauseRef, learned_ref.items, self, Self.clauseLessThan);

            const db_size: f64 = @floatFromInt(self.learned_clauses.len());
            var limit: usize = @intFromFloat(fraction * db_size);
            var arena = std.heap.ArenaAllocator.init(self.allocator);
            var allocator = arena.allocator();

            var i: usize = 0;
            for (learned_ref.items) |cref| {
                var clause = self.borrow(cref);

                var delete = i < limit; // and clause.stats.Learned.lbd >= 3;

                if (clause.lock == 0 and delete) {
                    self.learned_clauses.free(cref.id);
                    i += 1;
                } else {
                    var expr = try allocator.alloc(Lit, clause.expr.len);
                    std.mem.copy(Lit, expr, clause.expr);
                    clause.expr = expr;
                }
            }

            self.main_arena.deinit();
            self.main_arena = arena;
        }

        pub fn decrLock(self: *Self, cref: ClauseRef) void {
            self.borrow(cref).lock -= 1;
        }

        pub fn incrLock(self: *Self, cref: ClauseRef) void {
            self.borrow(cref).lock += 1;
        }

        pub fn deinitClause(self: *Self, cref: ClauseRef) void {
            self.allocator.free(cref.expr);
            self.allocator.destroy(cref);
        }
    };
}

test "random clause manager test" {
    var rnd = std.rand.DefaultPrng.init(0);
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        _ = gpa.deinit();
    }

    var expr = std.ArrayList(Lit).init(allocator);
    defer expr.deinit();

    comptime var step = 0;
    var cm = ClauseDB(void).init(allocator);
    defer cm.deinit();
    inline while (step < 10) : (step += 1) {

        // create clauses
        var num_clauses: usize = 0;
        while (num_clauses < 100) : (num_clauses += 1) {
            var expr_size: usize = rnd.random().int(usize) % 10;

            while (expr_size > 0) : (expr_size -= 1) {
                var lit: Lit = undefined;

                if (rnd.random().int(u32) % 2 == 0) {
                    lit = Lit{ .pos = rnd.random().int(u31) };
                } else {
                    lit = Lit{ .neg = rnd.random().int(u31) };
                }

                try expr.append(lit);
            }

            _ = try cm.initClause(rnd.random().int(u32) % 2 == 0, expr.items, {});
            expr.clearRetainingCapacity();
        }

        var iter = cm.iter_learned();
        while (iter.next()) |cref| {
            var clause = cm.borrow(cref);
            var act = rnd.random().float(f64);
            clause.stats.Learned.activity = act;

            try std.testing.expect(cm.borrow(cref).stats.Learned.activity == act);
        }

        try cm.garbadgeCollect(0.7);
        std.debug.print("{}\n", .{cm.learned_clauses.len()});
    }
}
