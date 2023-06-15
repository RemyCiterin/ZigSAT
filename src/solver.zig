const std = @import("std");

// main data structure used by the solver
const Heap = @import("Heap.zig").Heap;
const IntSet = @import("IntSet.zig").IntSet;
const IntMap = @import("IntMap.zig").IntMap;

const VSIDS = @import("VSIDS.zig");

const LBDstats = @import("LBDstats.zig");

// representation of literals and possibly undefined boolean
const lbool = @import("lit.zig").lbool;
const Lit = @import("lit.zig").Lit;

// import clause and clause manager/garbadge collector
const Clause = @import("clause.zig").Clause;
const ClauseManager = @import("clause.zig").ClauseManager;
const ClauseRef = @import("clause.zig").ClauseRef;

// import theory solver to reason about theory like
// uninterpreted functions, linear arithmetic...
const TSolver = @import("theory_solver.zig").TSolver;

/// when a clause watch a variable (the variable is one of the two
/// first literals of it's expression), we store this clause
/// (to detect efficiently unit propagation) and
/// the other watcher literal (for optimization)
const Watcher = struct { cref: ClauseRef, blocker: Lit };

/// the state of an assigned literal is the decision level of the assignation,
/// the value of the assignation, and the clause at the origin of the assignation,
/// all the literals of this clause must be assigned to false and
/// `Lit.init(var, value)` must be a literal of this clause
const AssignedVarState = struct { level: u32, value: bool, reason: ?ClauseRef };

const Variable = @import("lit.zig").Variable;
pub const variableToUsize = @import("lit.zig").variableToUsize;

/// if a variable is not assigned, then no state is necessary
const VarState = ?AssignedVarState;

/// all the data of a variable store by the solver
const VarData = struct {
    /// state: assigned or not and why
    state: VarState,

    /// the list of all the watchers of the literal `Lit.init(variable, true)`
    pos_watchers: std.ArrayList(Watcher),

    /// the list of all the watchers of the literal `Lit.init(variable, false)`
    neg_watchers: std.ArrayList(Watcher),
};

const AnalyseData = struct {
    int_set: IntSet(Variable, variableToUsize),
    result: std.ArrayList(Lit),

    const Self = @This();
    fn init(allocator: std.mem.Allocator) Self {
        var self: Self = undefined;

        self.int_set = IntSet(Variable, variableToUsize).init(allocator);
        self.result = std.ArrayList(Lit).init(allocator);

        return self;
    }

    fn clear(self: *Self) void {
        self.result.clearRetainingCapacity();
        self.int_set.clear();
    }

    fn deinit(self: *Self) void {
        self.result.deinit();
        self.int_set.deinit();
    }
};

pub const SolverStats = struct {
    restart: usize,
    conflict: usize,
    gc: usize,
    prop: usize,

    const Self = @This();

    fn init() Self {
        var self: Self = undefined;
        self.restart = 0;
        self.gc = 0;
        self.conflict = 0;
        self.prop = 0;

        return self;
    }

    fn print(self: Self, progress: f64) void {
        std.debug.print("{} {} {} {}\n", .{ self.restart, self.conflict, self.prop, progress });
    }

    pub fn addRestart(self: *Self) void {
        self.restart += 1;
    }

    pub fn addGC(self: *Self) void {
        self.gc += 1;
    }

    pub fn numGC(self: *Self) usize {
        return self.gc;
    }

    pub fn addConflict(self: *Self) void {
        self.conflict += 1;
    }

    pub fn addPropagation(self: *Self) void {
        self.prop += 1;
    }
};

pub const Solver = struct {
    /// set of all the assignation of the solver, usefull for backtracking,
    /// if a literal `lit` is in the assignation queue, and `self.reasonOf(lit.variable()) != null`
    /// then all the negations of the literals in `self.reasonOf(lit.variable()).expr` are
    /// before `lit` in `self.assignation_queue`
    assignation_queue: std.ArrayList(Lit),

    /// buffer of literals to propagate, all the literals in it are also in
    /// `self.assignation_queue`
    propagation_queue: std.ArrayList(Lit),

    /// a ClauseManager for clause allocation and garbadge collection
    clause_manager: ClauseManager,

    /// set of variables and variables data
    variables: std.ArrayList(VarData),

    /// an IntSet to compute the lbd of a clause
    lbd_int_set: IntSet(u32, @import("Heap.zig").u32ToUsize),

    lbd_stats: LBDstats,

    /// an lbd to analyse the last conflict
    analyse_data: AnalyseData,

    /// an heap for VSIDS heuristic
    vsids: VSIDS,

    /// allocator of the solver
    allocator: std.mem.Allocator,

    /// if true then the solver state is unsat
    is_unsat: bool,

    /// current decision level of the solver
    level: u32,

    /// statistics of the solver (for profiling)
    stats: SolverStats,

    const Self = @This();
    const SolverError = std.mem.Allocator.Error || error{TooManyVariables};

    pub fn progressEstimate(self: *Self) f64 {
        var progress: f64 = 0.0;
        const F: f64 = 1.0 / @intToFloat(f64, self.variables.items.len);
        var level: usize = 0;

        for (self.assignation_queue.items) |l| {
            if (self.levelOf(l.variable()) != level)
                level = self.levelOf(l.variable());

            progress += std.math.pow(f64, F, @intToFloat(f64, level));
        }

        return progress / @intToFloat(f64, self.variables.items.len);
    }

    pub fn getLBD(self: *Self, expr: []const Lit) !usize {
        self.lbd_int_set.clear();

        for (expr) |lit| {
            try self.lbd_int_set.insert(self.levelOf(lit.variable()));
        }

        return self.lbd_int_set.len();
    }

    pub fn checkModel(self: *Self) bool {
        c_loop: for (self.clause_manager.initial_clauses.items) |cref| {
            for (cref.expr) |lit| {
                if (self.value(lit) == .ltrue) {
                    continue :c_loop;
                }
            }

            return false;
        }

        return true;
    }

    pub fn checkWatchersState(self: *Self) !void {
        for (self.variables.items) |var_data, variable| {
            var v = @intCast(Variable, variable);

            for (var_data.pos_watchers.items) |w| {
                try std.testing.expect(w.cref.expr[0].equals(Lit.init(v, true)) or
                    w.cref.expr[1].equals(Lit.init(v, true)));
            }

            for (var_data.neg_watchers.items) |w| {
                try std.testing.expect(w.cref.expr[0].equals(Lit.init(v, false)) or
                    w.cref.expr[1].equals(Lit.init(v, false)));
            }
        }
    }

    pub fn checkPropagateComplete(self: *Self) !void {
        c_loop: for (self.clause_manager.initial_clauses.items) |cref| {
            var count: usize = 0;

            for (cref.expr) |lit| {
                switch (self.value(lit)) {
                    .ltrue => continue :c_loop,
                    .lundef => count += 1,
                    .lfalse => {},
                }
            }

            try std.testing.expect(count >= 2);
        }
    }

    pub fn propagate(self: *Self) !?ClauseRef {
        while (self.propagation_queue.items.len > 0) {
            self.stats.addPropagation();

            if (try self.propagateLit(self.propagation_queue.pop())) |cref| {
                self.stats.addConflict();
                return cref;
            }
        }
        return null;
    }

    pub fn propagateLit(self: *Self, lit: Lit) !?ClauseRef {
        var watchers = self.getLitWatchers(lit.not());

        try std.testing.expect(self.value(lit) == .ltrue);

        var i: usize = 0;
        watchers_loop: while (i < watchers.items.len) {
            var blocker: Lit = watchers.items[i].blocker;
            var cref: ClauseRef = watchers.items[i].cref;

            if (self.value(blocker) == .ltrue) {
                i += 1;
                continue;
            }

            try std.testing.expect(!cref.is_deleted());

            if (cref.expr[0].equals(lit.not())) {
                std.mem.swap(Lit, &cref.expr[0], &cref.expr[1]);
            }

            try std.testing.expect(lit.not().equals(cref.expr[1]));

            blocker = cref.expr[0];
            watchers.items[i].blocker = blocker;

            if (self.value(blocker) == .ltrue) {
                i += 1;
                continue;
            }

            var k: usize = 2;
            while (k < cref.expr.len) : (k += 1) {
                //if (self.value(cref.expr[k]) == .ltrue) {
                //    i += 1;
                //    continue :watchers_loop;
                //}

                if (self.value(cref.expr[k]) != .lfalse) {
                    std.mem.swap(Lit, &cref.expr[k], &cref.expr[1]);
                    try self.getLitWatchers(cref.expr[1])
                        .append(Watcher{ .blocker = blocker, .cref = cref });
                    _ = watchers.swapRemove(i);

                    continue :watchers_loop;
                }
            }

            // did not find a new literal to watch:
            if (self.value(cref.expr[0]) == .lfalse) {
                //for (cref.expr) |l|
                //    try std.testing.expect(self.value(l) == .lfalse);

                self.propagation_queue.clearRetainingCapacity();
                return cref;
            }

            //try std.testing.expect(self.value(cref.expr[0]) == .lundef);
            //for (cref.expr) |l, index| {
            //    if (index != 0)
            //        try std.testing.expect(self.value(l) == .lfalse);
            //}

            try self.mkAssignation(cref.expr[0], cref);
            i += 1;
        }

        return null;
    }

    pub fn levelOf(self: *Self, variable: Variable) u32 {
        return self.variables.items[variable].state.?.level;
    }

    pub fn reasonOf(self: *Self, variable: Variable) ?ClauseRef {
        return self.variables.items[variable].state.?.reason;
    }

    pub fn analyse(self: *Self, cref: ClauseRef) !std.ArrayList(Lit) {
        var int_set = &self.analyse_data.int_set;
        var result = &self.analyse_data.result;
        self.analyse_data.clear();

        for (cref.expr) |lit|
            try std.testing.expect(self.value(lit) == .lfalse);

        try result.append(Lit.init(0, true));

        var IP_counter: usize = 0; // number of implication points of the current clause
        var index = self.assignation_queue.items.len - 1;
        var clause: ?ClauseRef = cref;
        var pivot: ?Lit = null;

        while (true) {
            self.clause_manager.incrActivity(clause.?);

            for (clause.?.expr) |lit| {
                if (pivot != null and pivot.?.equals(lit)) continue;
                try self.vsids.incrActivity(lit.variable());

                if (!int_set.inSet(lit.variable())) {
                    try int_set.insert(lit.variable());

                    if (self.levelOf(lit.variable()) < self.level) {
                        try result.append(lit);
                    } else {
                        IP_counter += 1;
                    }
                }
            }

            while (!int_set.inSet(self.assignation_queue.items[index].variable())) : (index -= 1) {}
            pivot = self.assignation_queue.items[index];
            clause = self.reasonOf(pivot.?.variable());
            int_set.remove(pivot.?.variable());
            result.items[0] = pivot.?.not();
            IP_counter -= 1;

            if (IP_counter == 0) break;
        }

        index = 1;
        minimize_loop: while (index < result.items.len) {
            var v = result.items[index].variable();

            var reason = self.reasonOf(v) orelse {
                index += 1;
                continue;
            };

            for (reason.expr) |l| {
                if (!int_set.inSet(l.variable())) {
                    index += 1;
                    continue :minimize_loop;
                }
            }

            _ = result.swapRemove(index);
        }

        try std.testing.expect(self.levelOf(result.items[0].variable()) == self.level);

        for (result.items) |l, i| {
            try std.testing.expect(self.value(l) == .lfalse);
            if (i != 0) try std.testing.expect(self.levelOf(l.variable()) < self.level);
        }

        return result.*;
    }

    pub fn print(self: *Self) void {
        self.clause_manager.printDB();

        std.debug.print("assignation queue\n", .{});
        for (self.assignation_queue.items) |lit| {
            var x: i64 = @intCast(i64, lit.variable());
            var y = if (lit.sign()) x else -x;
            std.debug.print("{} ", .{y});
        }
        std.debug.print("\n", .{});
    }

    pub fn value(self: *Self, lit: Lit) lbool {
        var st: VarState = self.variables.items[lit.variable()].state;

        if (st == null) return .lundef;

        return lbool.init(st.?.value == lit.sign());
    }

    pub fn removeClause(self: *Self, cref: ClauseRef) void {
        self.detachClause(cref);

        for (cref.expr) |lit| {
            if (self.value(lit) == .ltrue and self.reasonOf(lit.variable()) == cref)
                self.variables.items[lit.variable()].state.?.reason = null;
        }
    }

    pub fn simplify(self: *Self) !void {
        try std.testing.expect(self.level == 0);

        var index: usize = 0;
        main_loop: while (index < self.clause_manager.learned_clauses.items.len) {
            var cref = self.clause_manager.learned_clauses.items[index];

            for (cref.expr) |lit| {
                if (self.value(lit) == .ltrue) {
                    _ = self.clause_manager.learned_clauses.swapRemove(index);
                    cref.stats.Learned.is_deleted = true;
                    self.removeClause(cref);
                    continue :main_loop;
                }
            }

            index += 1;
        }

        //index = 0;
        //main_loop: while (index < self.clause_manager.initial_clauses.items.len) {
        //    var cref = self.clause_manager.initial_clauses.items[index];

        //    for (cref.expr) |lit| {
        //        if (self.value(lit) == .ltrue) {
        //            self.removeClause(cref);
        //            _ = self.clause_manager.initial_clauses.swapRemove(index);
        //            self.clause_manager.deinitClause(cref);
        //            continue :main_loop;
        //        }
        //    }

        //    index += 1;
        //}
    }

    pub fn addLearnedClause(self: *Self, expr: []Lit) !ClauseRef {
        try std.testing.expect(expr.len >= 2);

        var cref = try self.clause_manager.initClause(true, expr);
        try self.attachClause(cref);
        return cref;
    }

    /// the expression is borrow by the caller, the caller must deinit it
    pub fn addClause(self: *Self, expr: []Lit) !void {
        try std.testing.expect(self.level == 0);

        if (self.is_unsat) {
            // the formula is already unsat
            return;
        }

        const sortFn = struct {
            fn lessThan(ctx: void, l1: Lit, l2: Lit) bool {
                _ = ctx;

                if (l1.variable() != l2.variable())
                    return l1.variable() < l2.variable();

                return l1.sign() and !l2.sign();
            }
        };

        var new_expr = std.ArrayList(Lit).init(self.allocator);
        defer new_expr.deinit();

        std.sort.sort(Lit, new_expr.items, {}, sortFn.lessThan);

        var i: usize = 0;
        var l: ?Lit = null;
        while (i < expr.len) : (i += 1) {
            if ((l != null and expr[i].equals(l.?.not())) or self.value(expr[i]) == .ltrue)
                return;

            if (self.value(expr[i]) != .lfalse and (l == null or !expr[i].equals(l.?))) {
                try new_expr.append(expr[i]);
                l = expr[i];
            }
        }

        if (new_expr.items.len == 0) {
            self.is_unsat = true;
            return;
        }

        if (new_expr.items.len == 1) {
            try self.mkAssignation(new_expr.items[0], null);
        } else {
            var cref = try self.clause_manager.initClause(false, new_expr.items);
            for (cref.expr) |lit|
                try self.vsids.incrActivity(lit.variable());
            try self.attachClause(cref);
        }
    }

    pub fn lastAssignation(self: *Self) ?Lit {
        var l = self.assignation_queue.items.len;

        if (l == 0) return null;
        return self.assignation_queue.items[l - 1];
    }

    fn mkAssignation(self: *Self, lit: Lit, cref: ?ClauseRef) !void {
        if (cref) |clause|
            for (clause.expr) |l|
                if (l.variable() != lit.variable())
                    try std.testing.expect(self.value(l) == .lfalse);

        try std.testing.expect(self.value(lit) == .lundef);

        try self.assignation_queue.append(lit);
        try self.propagation_queue.append(lit);

        var st = .{ .level = self.level, .reason = cref, .value = lit.sign() };

        if (cref != null) {
            self.clause_manager.incrLock(cref.?);
        }

        self.variables.items[lit.variable()].state = st;
        try self.vsids.setState(lit.variable(), lbool.init(lit.sign()));
    }

    fn dequeueAssignation(self: *Self) !Lit {
        var lit = self.assignation_queue.pop();
        try std.testing.expect(self.value(lit) == .ltrue);

        var cref = self.variables.items[lit.variable()].state.?.reason;

        if (cref != null) {
            self.clause_manager.decrLock(cref.?);
        } else {
            if (self.level != 0)
                self.level -= 1;
        }

        self.variables.items[lit.variable()].state = null;

        try self.vsids.setState(lit.variable(), .lundef);

        return lit;
    }

    pub fn restart(self: *Self) !void {
        self.propagation_queue.clearRetainingCapacity();
        self.lbd_stats.clear();
        self.stats.addRestart();
        while (true) {
            if (self.lastAssignation()) |lit| {
                if (self.levelOf(lit.variable()) == 0)
                    break;

                _ = try self.dequeueAssignation();
            } else break;
        }
    }

    pub fn cdcl(self: *Self) !bool {
        while (true) {
            if (try self.propagate()) |cref| {
                if (self.level == 0) return false;

                var num_assign = self.assignation_queue.items.len;
                try self.lbd_stats.addNumAssign(num_assign);

                var new_expr = try self.analyse(cref);

                var lbd = 1 + try self.getLBD(new_expr.items);
                try self.lbd_stats.append(lbd, new_expr.items.len);

                var level: u32 = 0;
                for (new_expr.items) |lit| {
                    var v = lit.variable();
                    var v_level = self.levelOf(v);
                    if (v_level < self.level) level = std.math.max(level, v_level);
                }

                while (true) {
                    if (self.lastAssignation()) |lit| {
                        if (self.levelOf(lit.variable()) <= level)
                            break;

                        _ = try self.dequeueAssignation();
                    } else break;
                }

                if (new_expr.items.len == 1) {
                    try self.mkAssignation(new_expr.items[0], null);
                } else {
                    var new_clause = try self.addLearnedClause(new_expr.items);
                    try self.mkAssignation(new_expr.items[0], new_clause);
                    self.clause_manager.incrActivity(new_clause);
                }

                self.clause_manager.decayActivity();
                self.vsids.decayActivity();

                if (self.lbd_stats.needRestart())
                    try self.restart();
            } else {
                var db_len = self.clause_manager.learned_clauses.items.len;
                if (db_len > 20000 + 500 * self.stats.numGC())
                    try self.garbadgeCollect(0.5);

                if (self.level == 0)
                    try self.simplify();

                var decision = self.vsids.mkDecision() orelse return true;
                self.level += 1;

                try self.mkAssignation(decision, null);
            }
        }
    }

    fn getLitWatchers(self: *Self, lit: Lit) *std.ArrayList(Watcher) {
        if (lit.sign()) {
            return &self.variables.items[lit.variable()].pos_watchers;
        } else {
            return &self.variables.items[lit.variable()].neg_watchers;
        }
    }

    fn attachClause(self: *Self, cref: ClauseRef) !void {
        var w0 = Watcher{ .blocker = cref.expr[1], .cref = cref };
        var w1 = Watcher{ .blocker = cref.expr[0], .cref = cref };

        try self.getLitWatchers(cref.expr[0]).append(w0);
        try self.getLitWatchers(cref.expr[1]).append(w1);
    }

    fn detachClause(self: *Self, cref: ClauseRef) void {
        var ws0 = self.getLitWatchers(cref.expr[0]);
        var ws1 = self.getLitWatchers(cref.expr[1]);

        var i: usize = 0;

        while (true) : (i += 1) {
            if (ws0.items[i].cref == cref) {
                _ = ws0.swapRemove(i);
                break;
            }
        }

        i = 0;

        while (true) : (i += 1) {
            if (ws1.items[i].cref == cref) {
                _ = ws1.swapRemove(i);
                break;
            }
        }
    }

    /// init a new solver, call `deinit()` to free it's memory
    pub fn init(allocator: std.mem.Allocator) !Self {
        var self: Self = undefined;

        self.clause_manager = ClauseManager.init(allocator);
        self.propagation_queue = std.ArrayList(Lit).init(allocator);
        self.assignation_queue = std.ArrayList(Lit).init(allocator);
        self.variables = std.ArrayList(VarData).init(allocator);
        self.lbd_int_set = IntSet(u32, @import("Heap.zig").u32ToUsize)
            .init(allocator);
        self.vsids = VSIDS.init(allocator);

        self.analyse_data = AnalyseData.init(allocator);
        self.lbd_stats = try LBDstats.init(allocator);

        self.allocator = allocator;
        self.is_unsat = false;
        self.level = 0;

        self.stats = SolverStats.init();

        return self;
    }

    /// remove the `1 - factor` fraction of less usefull learned clauses
    /// and all the link from the solver for these clauses
    pub fn garbadgeCollect(self: *Self, factor: f64) !void {
        self.stats.addGC();

        try self.clause_manager.garbadgeCollect(factor);
        std.debug.print("{} ", .{self.lbd_stats.mean_size});
        self.stats.print(self.progressEstimate());

        for (self.variables.items) |*var_data| {
            var i: usize = 0;

            while (i < var_data.pos_watchers.items.len) {
                var cref = var_data.pos_watchers.items[i].cref;
                if (cref.is_deleted()) {
                    _ = var_data.pos_watchers.swapRemove(i);
                } else {
                    if (cref.newAddr()) |new_addr|
                        var_data.pos_watchers.items[i].cref = new_addr;
                    i += 1;
                }
            }

            i = 0;
            while (i < var_data.neg_watchers.items.len) {
                var cref = var_data.neg_watchers.items[i].cref;
                if (cref.is_deleted()) {
                    _ = var_data.neg_watchers.swapRemove(i);
                } else {
                    if (cref.newAddr()) |new_addr| {
                        var_data.neg_watchers.items[i].cref = new_addr;
                    }
                    i += 1;
                }
            }

            if (var_data.state) |st| {
                if (st.reason) |reason| {
                    if (reason.newAddr()) |new_addr|
                        var_data.state.?.reason = new_addr;
                }
            }
        }

        self.clause_manager.applyGC();
    }

    /// free all the memory of the solver
    pub fn deinit(self: *Self) void {
        self.propagation_queue.deinit();
        self.assignation_queue.deinit();
        self.analyse_data.deinit();
        self.lbd_int_set.deinit();
        self.lbd_stats.deinit();
        self.vsids.deinit();

        for (self.variables.items) |*var_data| {
            var_data.pos_watchers.deinit();
            var_data.neg_watchers.deinit();
        }

        self.variables.deinit();
        self.clause_manager.deinit();
    }

    /// create a new variable and initialize all it's states
    pub fn addVariable(self: *Self) SolverError!u31 {
        var new_var_usize = self.variables.items.len;

        if (new_var_usize != (new_var_usize & ((2 << 31) - 1))) {
            return error.TooManyVariables;
        }

        var new_var = @truncate(u31, new_var_usize);

        var new_var_data: VarData = undefined;
        new_var_data.state = null;
        new_var_data.pos_watchers =
            std.ArrayList(Watcher).init(self.allocator);
        new_var_data.neg_watchers =
            std.ArrayList(Watcher).init(self.allocator);

        try self.variables.append(new_var_data);
        try self.vsids.addVariable();

        return new_var;
    }

    pub fn printDIMACS(self: *Self) void {
        const num_v = self.variables.items.len;
        const num_c = self.clause_manager.initial_clauses.items.len;

        std.debug.print("p {} {}\n", .{ num_v - 1, num_c });

        for (self.clause_manager.initial_clauses.items) |cref| {
            for (cref.expr) |lit| {
                var v: i64 = @as(i64, lit.variable());
                if (v == 0) continue;
                if (lit.sign()) {
                    std.debug.print("{} ", .{v});
                } else {
                    std.debug.print("-{} ", .{v});
                }
            }
            std.debug.print("0\n", .{});
        }
    }

    pub fn parse(self: *Self, text: []u8) !void {
        var index: usize = 0;

        const IntParser = struct {
            index: usize,
            text: []u8,

            fn parseInternal(state: *@This(), x: i64) ?i64 {
                if (state.index >= state.text.len) return x;
                var char = state.text[state.index];

                switch (char) {
                    '0'...'9' => {
                        var y = char - '0';
                        state.index += 1;
                        return state.parseInternal(x * 10 + y);
                    },
                    ' ', '\n', '\t' => return x,
                    else => return null,
                }
            }

            fn parse(state: *@This()) ?i64 {
                if (state.index >= state.text.len) return null;
                switch (state.text[state.index]) {
                    '0'...'9' => return state.parseInternal(0),
                    '-' => {
                        state.index += 1;
                        var x = state.parse() orelse return null;
                        return -x;
                    },
                    else => return null,
                }
            }
        };

        var expr = std.ArrayList(Lit).init(self.allocator);
        defer expr.deinit();

        while (index < text.len) {
            if (text[index] == ' ' or text[index] == '\t' or text[index] == '\n') {
                index += 1;
                continue;
            }

            // parse comment
            if (text[index] == 'c' or text[index] == 'p') {
                while (index < text.len and text[index] != '\n')
                    index += 1;
                continue;
            }
            // parse clause
            while (index < text.len) {
                if (text[index] == ' ' or text[index] == '\n' or text[index] == '\t') {
                    index += 1;
                    continue;
                }

                var p = IntParser{ .index = index, .text = text };
                var lit = p.parse() orelse unreachable;
                index = p.index;

                if (lit == 0) break;

                var variable = if (lit > 0) lit else -lit;

                while (self.variables.items.len <= variable) {
                    _ = try self.addVariable();
                }

                try expr.append(Lit.init(@intCast(Variable, variable), lit > 0));
            }

            try self.addClause(expr.items);
            expr.clearRetainingCapacity();
        }

        return;
    }
};

test "random clause manager test" {
    //var rnd = std.rand.DefaultPrng.init(0);
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        _ = gpa.deinit();
    }

    var expr = std.ArrayList(Lit).init(allocator);
    defer expr.deinit();

    const iter_dir = try std.fs.cwd().openIterableDir("tests_competition", .{});
    std.debug.print("\n", .{});

    var iter = iter_dir.iterate();
    var index: usize = 0;

    while (try iter.next()) |entry| : (index += 1) {
        if (entry.kind == .File) {
            var solver = try Solver.init(allocator);
            defer solver.deinit();

            const file_path =
                try std.fmt.allocPrint(allocator, "tests_competition/{s}", .{entry.name});
            std.debug.print("{s}\n", .{file_path});
            defer allocator.free(file_path);

            const file = try std.fs.cwd().openFile(file_path, .{});
            defer file.close();

            const file_size = try file.getEndPos();

            var buffer = try allocator.alloc(u8, file_size);
            defer allocator.free(buffer);

            var bytes_read = try file.read(buffer);

            try std.testing.expect(bytes_read == buffer.len);

            try solver.parse(buffer);

            var skip_file = false;
            for ("sudoku.cnf") |c, i| {
                if (i >= entry.name.len or entry.name[i] != c) {
                    skip_file = true;
                    break;
                }
            }

            //if (!skip_file) continue;

            var b = try solver.cdcl();
            if (b) try std.testing.expect(solver.checkModel());
            std.debug.print("{}\n", .{b});

            if (!b) {
                const result = try std.ChildProcess.exec(.{
                    .allocator = std.heap.page_allocator,
                    .argv = &[_][]const u8{
                        "z3",
                        file_path,
                    },
                });
                std.debug.print("{s}\n", .{result.stdout});
            }
        }
    }
}
