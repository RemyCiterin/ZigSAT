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

    /// for detach it's watched literals if the clause is deleted at GC
    is_deleted: bool = false,

    /// a reference to itself or it's new location
    cref: *Clause,
};

pub const ClauseStats = union(enum) {
    Learned: LearnedClauseStats,
    Initial,
};

/// clause description
pub const Clause = struct {
    /// statistics of the clause
    stats: ClauseStats,

    /// expression of the clause, the two firsts literals are named
    /// watched literals, they change with time
    expr: []Lit,

    /// the garbadge collector cannot delete a learned clause if lock is strictly positive
    lock: u32,

    pub fn is_deleted(self: @This()) bool {
        switch (self.stats) {
            .Learned => |lcs| return lcs.is_deleted,
            else => return false,
        }
    }

    pub fn newAddr(self: @This()) ?*@This() {
        switch (self.stats) {
            .Learned => |lcs| return lcs.cref,
            else => return null,
        }
    }

    pub fn setLBD(self: *@This(), lbd: usize) void {
        switch (self.stats) {
            .Learned => |*lcs| lcs.lbd = lbd,
            else => {},
        }
    }
};

pub const ClauseManager = struct {
    pub const ClauseRef = *Clause;

    /// allocator for the diffents arena allocators
    allocator: std.mem.Allocator,

    /// arena allocator
    main_allocator: std.heap.ArenaAllocator,

    /// transition arena allocator, for reallocation
    transition_allocator: std.heap.ArenaAllocator,

    /// list of used learned clause by the solver
    learned_clauses: std.ArrayList(ClauseRef),

    /// list of initial clause used by the solver
    initial_clauses: std.ArrayList(ClauseRef),

    // /// set of deleted clause, call applyGC to delete
    // deleted_clauses: std.ArrayList(ClauseRef),

    /// clause activity decay factor
    activity_decay_factor: f64,

    /// current activity add at each call of incrActivity
    activity_increment: f64,

    const Self = @This();

    /// initialize a clause manager
    pub fn init(allocator: std.mem.Allocator) Self {
        var self: Self = undefined;
        self.learned_clauses = std.ArrayList(ClauseRef).init(allocator);
        self.initial_clauses = std.ArrayList(ClauseRef).init(allocator);
        //self.deleted_clauses = std.ArrayList(ClauseRef).init(allocator);
        self.transition_allocator = std.heap.ArenaAllocator.init(allocator);
        self.main_allocator = std.heap.ArenaAllocator.init(allocator);
        self.activity_decay_factor = 0.999;
        self.activity_increment = 1.0;
        self.allocator = allocator;
        return self;
    }

    /// free it's database but not it's clauses
    pub fn deinit(self: *Self) void {
        self.applyGC();

        for (self.initial_clauses.items) |cref| {
            self.deinitClause(cref);
        }

        self.main_allocator.deinit();
        self.transition_allocator.deinit();

        self.learned_clauses.deinit();
        self.initial_clauses.deinit();
    }

    /// this function clone the expression
    /// the caller have to dealloc it itself
    pub fn initClause(self: *Self, is_learned: bool, expr: []const Lit) !ClauseRef {
        var new_expr: []Lit = undefined;
        var clause: ClauseRef = undefined;

        if (is_learned) {
            new_expr = try self.main_allocator.allocator().alloc(Lit, expr.len);
            clause = try self.main_allocator.allocator().create(Clause);

            try self.learned_clauses.append(clause);

            var st = LearnedClauseStats{ .cref = clause };
            clause.stats = ClauseStats{ .Learned = st };
        } else {
            new_expr = try self.allocator.alloc(Lit, expr.len);
            clause = try self.allocator.create(Clause);

            try self.initial_clauses.append(clause);

            clause.stats = ClauseStats.Initial;
        }

        std.mem.copy(Lit, new_expr, expr);

        clause.expr = new_expr;
        clause.lock = 0;

        return clause;
    }

    pub fn incrActivity(self: *Self, cref: ClauseRef) void {
        if (cref.stats == .Initial) return;

        cref.stats.Learned.activity += self.activity_increment;

        if (cref.stats.Learned.activity > 1e20) {
            for (self.learned_clauses.items) |c| {
                c.stats.Learned.activity *= 1e-20;
            }
            self.activity_increment *= 1e-20;
        }
    }

    pub fn decayActivity(self: *Self) void {
        self.activity_increment *= 1.0 / self.activity_decay_factor;
    }

    pub fn printClause(self: *Self, cref: ClauseRef) void {
        _ = self;
        for (cref.expr) |lit| {
            var x: i64 = @intCast(lit.variable());
            var y: i64 = if (lit.sign()) x else -x;
            std.debug.print("{} ", .{y});
        }
        std.debug.print("\n", .{});
    }

    pub fn printDB(self: *Self) void {
        std.debug.print("initial clauses\n", .{});

        for (self.initial_clauses.items) |clause| {
            self.printClause(clause);
        }

        std.debug.print("learned clauses\n", .{});

        for (self.learned_clauses.items) |clause| {
            self.printClause(clause);
        }
    }

    fn clauseLessThan(context: void, lhs: ClauseRef, rhs: ClauseRef) bool {
        _ = context;
        if (lhs.stats.Learned.lbd != rhs.stats.Learned.lbd)
            return lhs.stats.Learned.lbd < rhs.stats.Learned.lbd;

        if (lhs.expr.len != rhs.expr.len)
            return lhs.expr.len < rhs.expr.len;

        return lhs.stats.Learned.activity > rhs.stats.Learned.activity;
    }

    /// `fraction` is the fraction of clauses we keep the database,
    /// set the deleted clauses to deleted, call applyGC to delete it
    pub fn garbadgeCollect(self: *Self, fraction: f64) !void {
        std.mem.sort(ClauseRef, self.learned_clauses.items, {}, Self.clauseLessThan);

        const db_size: f64 = @floatFromInt(self.learned_clauses.items.len);
        var limit: usize = @intFromFloat(fraction * db_size);
        var arena = self.transition_allocator.allocator();

        var i: usize = 0;
        while (i < self.learned_clauses.items.len) {
            var cref: ClauseRef = self.learned_clauses.items[i];

            var delete = i > limit and cref.expr.len >= 3 and cref.stats.Learned.lbd >= 3;

            if (cref.lock == 0 and (delete or cref.is_deleted())) {
                _ = self.learned_clauses.swapRemove(i);
                cref.stats.Learned.is_deleted = true;
            } else {
                var expr = try arena.alloc(Lit, cref.expr.len);
                std.mem.copy(Lit, expr, cref.expr);
                cref.expr = expr;

                var new_cref = try arena.create(Clause);
                cref.stats.Learned.cref = new_cref;
                new_cref.* = cref.*;

                self.learned_clauses.items[i] = new_cref;
                i += 1;
            }
        }
    }

    pub fn applyGC(self: *Self) void {
        self.main_allocator.deinit();
        self.main_allocator = self.transition_allocator;
        self.transition_allocator = std.heap.ArenaAllocator.init(self.allocator);
    }

    pub fn decrLock(self: *Self, cref: ClauseRef) void {
        cref.lock -= 1;
        _ = self;
    }

    pub fn incrLock(self: *Self, cref: ClauseRef) void {
        cref.lock += 1;
        _ = self;
    }

    pub fn deinitClause(self: *Self, cref: ClauseRef) void {
        self.allocator.free(cref.expr);
        self.allocator.destroy(cref);
    }
};

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
    inline while (step < 10) : (step += 1) {
        var cm = ClauseManager.init(allocator);
        defer cm.deinit();

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

            _ = try cm.initClause(rnd.random().int(u32) % 2 == 0, expr.items);
            expr.clearRetainingCapacity();
        }

        for (cm.learned_clauses.items) |cref| {
            cref.stats.Learned.activity = rnd.random().float(f64);
        }

        try cm.garbadgeCollect(0.7);
        cm.applyGC();
    }
}
