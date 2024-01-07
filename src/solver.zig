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
const ClauseDB = @import("clause.zig").ClauseDB;
const Clause = @import("clause.zig").Clause;

// import theory solver to reason about theory like
// uninterpreted functions, linear arithmetic...
const TSolver = @import("theory_solver.zig").TSolver;

const generateClause = @import("lit.zig").generateClause;

/// when a clause watch a variable (the variable is one of the two
/// first literals of it's expression), we store this clause
/// (to detect efficiently unit propagation) and
/// the other watcher literal (for optimization)
pub fn Watcher(comptime ClauseRef: type) type {
    return struct { cref: ClauseRef, blocker: Lit };
}

/// the state of an assigned literal is the decision level of the assignation,
/// the value of the assignation, and the clause at the origin of the assignation,
/// all the literals of this clause must be assigned to false and
/// `Lit.init(var, value)` must be a literal of this clause
pub fn AssignedVarState(comptime ClauseRef: type, comptime P: type) type {
    return struct {
        level: u32,
        value: bool,
        reason: ?ClauseRef,
        proof: ?P,
        position: usize,
    };
}

const Variable = @import("lit.zig").Variable;
pub const variableToUsize = @import("lit.zig").variableToUsize;

/// all the data of a variable store by the solver
fn VarData(comptime ClauseRef: type, comptime P: type) type {
    return struct {
        /// state: assigned or not and why
        state: ?AssignedVarState(ClauseRef, P),

        /// the list of all the watchers of the literal `Lit.init(variable, true)`
        pos_watchers: std.ArrayList(Watcher(ClauseRef)),

        /// the list of all the watchers of the literal `Lit.init(variable, false)`
        neg_watchers: std.ArrayList(Watcher(ClauseRef)),
    };
}

pub const SolverStats = struct {
    restart: usize,
    conflict: usize,
    gc: usize,
    prop: usize,

    const Self = @This();

    fn init() Self {
        return Self{
            .restart = 0,
            .gc = 0,
            .conflict = 0,
            .prop = 0,
        };
    }

    pub fn print(self: Self, progress: f64) void {
        std.debug.print("{}  {}  {}  {}\n", .{ self.restart, self.conflict, self.prop, progress });
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

    pub fn numConflict(self: Self) usize {
        return self.conflict;
    }

    pub fn addPropagation(self: *Self) void {
        self.prop += 1;
    }
};

pub fn Solver(comptime ProofManager: type) type {
    comptime {
        @import("trait.zig").Trait(ProofManager, .{
            .{ "Proof", type },
            .{ "addAxiom", fn (*ProofManager, []Lit) void },
            .{ "initResolution", fn (*ProofManager, ProofManager.Proof) void },
            .{ "pushResolutionStep", fn (*ProofManager, Variable, ProofManager.Proof) void },
            .{ "finalizeResolution", fn (*ProofManager) ProofManager.Proof },
        });
    }

    return struct {
        pub const Proof = ProofManager.Proof;
        pub const ClauseRef = ClauseDB(Proof).ClauseRef;

        /// set of all the assignation of the solver, usefull for backtracking,
        /// if a literal `lit` is in the assignation queue, and `self.reasonOf(lit.variable()) != null`
        /// then all the negations of the literals in `self.reasonOf(lit.variable()).expr` are
        /// before `lit` in `self.assignation_queue`
        assignation_queue: std.ArrayList(Lit),

        /// buffer of literals to propagate, all the literals in it are also in
        /// `self.assignation_queue`
        propagation_queue: std.ArrayList(Lit),

        /// a ClauseDB for clause allocation and garbadge collection
        clause_db: ClauseDB(Proof),

        /// set of variables and variables data
        variables: std.ArrayList(VarData(ClauseRef, Proof)),

        /// use and compute lbd
        lbd_stats: LBDstats,

        /// result of the final analysis
        final_conflict: std.ArrayList(Lit),

        /// an heap for VSIDS heuristic
        vsids: VSIDS,

        /// level of verbosity
        verbose: i32,

        /// allocator of the solver
        allocator: std.mem.Allocator,

        /// if true then the solver state is unsat
        is_unsat: ?Proof,

        /// current decision level of the solver
        level: u32,

        /// statistics of the solver (for profiling)
        stats: SolverStats,

        /// construct resolution chains
        proof_manager: ProofManager,

        /// set of variables seen during analyze
        seen: IntSet(Variable, variableToUsize),

        /// result of analyze call
        analyze_result: std.ArrayList(Lit),

        const Self = @This();
        const SolverError = std.mem.Allocator.Error || error{TooManyVariables};

        /// print the current solving progress of the solver
        pub fn progressEstimate(self: *Self) f64 {
            var progress: f64 = 0.0;
            const F: f64 = 1.0 / @as(f64, @floatFromInt(self.variables.items.len));
            var level: usize = 0;

            for (self.assignation_queue.items) |l| {
                if (self.levelOf(l.variable()) != level)
                    level = self.levelOf(l.variable());

                progress += std.math.pow(f64, F, @as(f64, @floatFromInt(level)));
            }

            return progress / @as(f64, @floatFromInt(self.variables.items.len));
        }

        /// check if the current model satisfy all the initial clauses
        pub fn checkModel(self: *Self) bool {
            var iter = self.clause_db.iter_initial();
            c_loop: while (iter.next()) |cref| {
                var clause = self.clause_db.borrow(cref);
                for (clause.expr) |lit| {
                    if (self.value(lit) == .ltrue) {
                        continue :c_loop;
                    }
                }

                return false;
            }

            return true;
        }

        pub fn checkWatchersState(self: *Self) !void {
            for (self.variables.items, 0..) |var_data, variable| {
                var v: Variable = @intCast(variable);

                for (var_data.pos_watchers.items) |w| {
                    var clause = self.clause_db.borrow(w.cref);
                    try std.testing.expect(clause.expr[0].equals(Lit.init(v, true)) or
                        clause.expr[1].equals(Lit.init(v, true)));
                }

                for (var_data.neg_watchers.items) |w| {
                    var clause = self.clause_db.borrow(w.cref);
                    try std.testing.expect(clause.expr[0].equals(Lit.init(v, false)) or
                        clause.expr[1].equals(Lit.init(v, false)));
                }
            }
        }

        /// check if their is still a variable to assign using the current clauses
        pub fn checkPropagateComplete(self: *Self) !void {
            var initial = self.clause_db.iter_initial();
            c_loop: while (initial.next()) |cref| {
                var clause = self.clause_db.borrow(cref);
                var count: usize = 0;

                for (clause.expr) |lit| {
                    switch (self.value(lit)) {
                        .ltrue => continue :c_loop,
                        .lundef => count += 1,
                        .lfalse => {},
                    }
                }

                try std.testing.expect(count >= 2);
            }
        }

        /// propagate all the assigned variables and see if their is a conflict
        fn propagate(self: *Self) !?ClauseRef {
            while (self.propagation_queue.items.len > 0) {
                self.stats.addPropagation();

                if (try self.propagateLit(self.propagation_queue.pop())) |cref| {
                    return cref;
                }
            }
            return null;
        }

        /// use the watcher lists to propagate the assignation of a variable inside the solver
        fn propagateLit(self: *Self, lit: Lit) !?ClauseRef {
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

                try std.testing.expect(!self.clause_db.is_free(cref));
                var clause = self.clause_db.borrow(cref);

                if (clause.expr[0].equals(lit.not())) {
                    std.mem.swap(Lit, &clause.expr[0], &clause.expr[1]);
                }

                try std.testing.expect(lit.not().equals(clause.expr[1]));

                blocker = clause.expr[0];
                watchers.items[i].blocker = blocker;

                if (self.value(blocker) == .ltrue) {
                    i += 1;
                    continue;
                }

                var k: usize = 2;
                while (k < clause.expr.len) : (k += 1) {
                    if (self.value(clause.expr[k]) != .lfalse) {
                        std.mem.swap(Lit, &clause.expr[k], &clause.expr[1]);
                        try self.getLitWatchers(clause.expr[1])
                            .append(Watcher(ClauseRef){ .blocker = blocker, .cref = cref });
                        _ = watchers.swapRemove(i);

                        continue :watchers_loop;
                    }
                }

                // did not find a new literal to watch:
                if (self.value(clause.expr[0]) == .lfalse) {
                    self.propagation_queue.clearRetainingCapacity();
                    return cref;
                }

                var proof: ?Proof = null;

                if (self.level == 0) {
                    self.proof_manager.initResolution(clause.proof);

                    for (1..clause.expr.len) |idx| {
                        var v = clause.expr[idx].variable();
                        self.proof_manager.pushResolutionStep(v, self.proofOf(v).?);
                    }

                    proof = self.proof_manager.finalizeResolution();
                }

                try self.mkAssignation(clause.expr[0], if (self.level == 0) null else cref, proof);
                i += 1;
            }

            return null;
        }

        /// return the level of assignation of an assigned variable
        pub fn levelOf(self: Self, variable: Variable) u32 {
            return self.variables.items[variable].state.?.level;
        }

        pub fn reasonOf(self: Self, variable: Variable) ?ClauseRef {
            return self.variables.items[variable].state.?.reason;
        }

        /// return a proof of assignation of an assigned variable, if `self.levelOf(v) == 0`
        pub fn proofOf(self: Self, variable: Variable) ?Proof {
            return self.variables.items[variable].state.?.proof;
        }

        pub fn print(self: *Self) void {
            self.clause_db.printDB();

            std.debug.print("assignation queue\n", .{});
            for (self.assignation_queue.items) |lit| {
                var x: i64 = @intCast(lit.variable());
                var y = if (lit.sign()) x else -x;
                std.debug.print("{} ", .{y});
            }
            std.debug.print("\n", .{});
        }

        pub fn value(self: Self, lit: Lit) lbool {
            var st = self.variables.items[lit.variable()].state;

            if (st == null) return .lundef;
            return lbool.init(st.?.value == lit.sign());
        }

        pub fn simplify(self: *Self) !void {
            try std.testing.expect(self.level == 0);
            // now it just simplify the learned clauses, not the initial clauses

            var learned = self.clause_db.iter_learned();
            main_loop: while (learned.next()) |cref| {
                var clause = self.clause_db.borrow(cref);

                for (clause.expr) |lit| {
                    if (self.value(lit) == .ltrue) {
                        self.proof_manager.release(clause.proof);
                        self.detachClause(cref);
                        self.clause_db.free(cref);
                        continue :main_loop;
                    }
                }

                self.proof_manager.initResolution(clause.proof);
                self.proof_manager.release(clause.proof);

                var i: usize = 2;
                while (i < clause.expr.len) {
                    var lit = clause.expr[i];
                    if (self.value(lit) == .lfalse) {
                        self.proof_manager.pushResolutionStep(lit.variable(), self.proofOf(lit.variable()).?);
                        std.mem.swap(Lit, &clause.expr[i], &clause.expr[clause.expr.len - 1]);
                        clause.expr.len -= 1;
                        continue;
                    }

                    i += 1;
                }

                clause.proof = self.proof_manager.finalizeResolution();
            }
        }

        fn addLearnedClause(self: *Self, expr: []const Lit, lbd: usize, proof: Proof) !ClauseRef {
            try std.testing.expect(expr.len >= 2);

            var cref = try self.clause_db.initClause(true, expr, proof);
            var clause = self.clause_db.borrow(cref);
            try self.attachClause(cref);
            clause.setLBD(lbd);
            return cref;
        }

        /// the expression is borrow by the caller, the caller must deinit it
        pub fn addClause(self: *Self, expr: *std.ArrayList(Lit)) !void { // []Lit) !void {
            try std.testing.expect(self.level == 0);

            if (self.is_unsat) |_| {
                // the formula is already unsat
                return;
            }
            if (try generateClause(expr))
                return;

            var proof = self.proof_manager.addAxiom(expr.items);

            var index: usize = 0;
            while (index < expr.items.len) {
                var lit = expr.items[index];
                if (self.value(lit) == .lfalse) {
                    self.proof_manager.pushResolutionStep(
                        lit.variable(),
                        self.proofOf(lit.variable()).?,
                    );
                    _ = expr.swapRemove(index);
                } else if (self.value(lit) == .ltrue) {
                    return;
                } else {
                    index += 1;
                }
            }

            proof = self.proof_manager.finalizeResolution();

            if (expr.items.len == 1) {
                try self.mkAssignation(expr.items[0], null, proof);
                if (try self.propagate()) |conf| {
                    var clause = self.clause_db.borrow(conf);
                    self.proof_manager.initResolution(clause.proof);
                    for (clause.expr) |lit| {
                        self.proof_manager.pushResolutionStep(
                            lit.variable(),
                            self.proofOf(lit.variable()).?,
                        );
                    }
                    self.is_unsat = self.proof_manager.finalizeResolution();
                }
                return;
            }

            if (expr.items.len == 0) {
                self.is_unsat = proof;
                return;
            }

            var cref = try self.clause_db.initClause(false, expr.items, proof);
            try self.attachClause(cref);
        }

        fn lastAssignation(self: *Self) ?Lit {
            var l = self.assignation_queue.items.len;

            if (l == 0) return null;
            return self.assignation_queue.items[l - 1];
        }

        fn mkAssignation(self: *Self, lit: Lit, cref: ?ClauseRef, proof: ?Proof) !void {
            if (cref) |c| {
                var clause = self.clause_db.borrow(c);
                for (clause.expr) |l|
                    if (l.variable() != lit.variable())
                        try std.testing.expect(self.value(l) == .lfalse);
            }

            try std.testing.expect(self.value(lit) == .lundef);

            if (cref) |_| try std.testing.expect(self.level > 0);
            if (self.level == 0) try std.testing.expect(proof != null);

            var st = .{
                .level = self.level,
                .reason = cref,
                .position = self.assignation_queue.items.len,
                .value = lit.sign(),
                .proof = proof,
            };

            try self.assignation_queue.append(lit);
            try self.propagation_queue.append(lit);

            if (cref != null) {
                self.clause_db.incrLock(cref.?);
            }

            self.variables.items[lit.variable()].state = st;
            try self.vsids.setState(lit.variable(), lbool.init(lit.sign()));
        }

        fn dequeueAssignation(self: *Self) !Lit {
            var lit = self.assignation_queue.pop();
            try std.testing.expect(self.value(lit) == .ltrue);

            var cref = self.variables.items[lit.variable()].state.?.reason;

            if (cref != null) {
                self.clause_db.decrLock(cref.?);
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

        pub fn backjump(self: *Self, learned: []Lit, proof: Proof) !void {
            var lbd = try self.lbd_stats.getLBD(self, learned);
            try self.lbd_stats.append(lbd, learned.len);

            var max_level = self.levelOf(learned[0].variable());

            var level: usize = 0;
            var ilevel: usize = 0;
            for (0.., learned) |i, lit| {
                var l = self.levelOf(lit.variable());

                if (l >= level and l < max_level) {
                    ilevel = i;
                    level = l;
                }
            }

            if (learned.len >= 2) std.mem.swap(Lit, &learned[1], &learned[ilevel]);

            while (self.lastAssignation()) |lit| {
                if (self.levelOf(lit.variable()) <= level)
                    break;

                _ = try self.dequeueAssignation();
            }

            if (learned.len == 1) {
                try self.mkAssignation(learned[0], null, proof);
            } else {
                var new_clause = try self.addLearnedClause(learned, lbd, proof);
                try self.mkAssignation(learned[0], new_clause, null);
                self.clause_db.incrActivity(new_clause);
            }

            self.clause_db.decayActivity();
            self.vsids.decayActivity();
        }

        pub fn cdcl(self: *Self, assumptions: []const Lit) !?Proof {
            self.final_conflict.clearRetainingCapacity();
            var restart_conflicts: usize = 0;
            try self.restart();

            try self.simplify();
            if (self.is_unsat) |proof| return proof;
            while (true) {
                if (try self.propagate()) |cref| {
                    if (self.level == 0) {
                        var clause = self.clause_db.borrow(cref);
                        self.proof_manager.initResolution(clause.proof);

                        for (clause.expr) |lit| {
                            self.proof_manager.pushResolutionStep(
                                lit.variable(),
                                self.proofOf(lit.variable()).?,
                            );
                        }

                        return self.proof_manager.finalizeResolution();
                    }

                    self.stats.addConflict();
                    restart_conflicts += 1;

                    var num_assign = self.assignation_queue.items.len;
                    try self.lbd_stats.addNumAssign(num_assign);

                    var new_expr = try self.analyze(cref);
                    var proof = self.proof_manager.finalizeResolution();

                    try self.backjump(new_expr, proof);
                } else {
                    if (self.lbd_stats.needRestart())
                        try self.restart();

                    if (restart_conflicts > 2000 + 300 * self.stats.numGC()) {
                        try self.garbadgeCollect(0.5);
                        restart_conflicts = 0;
                    }

                    //if (self.level == 0) try self.simplify();

                    var decision: ?Lit = null;

                    for (assumptions) |lit| {
                        if (self.value(lit) == .lfalse) {
                            @panic("unimplemented");
                        }

                        if (self.value(lit) == .lundef) {
                            decision = lit;
                            break;
                        }
                    }

                    if (decision == null)
                        decision = self.vsids.mkDecision() orelse return null;

                    self.level += 1;
                    try self.mkAssignation(decision.?, null, null);
                }
            }
        }

        fn getLitWatchers(self: *Self, lit: Lit) *std.ArrayList(Watcher(ClauseRef)) {
            if (lit.sign()) {
                return &self.variables.items[lit.variable()].pos_watchers;
            } else {
                return &self.variables.items[lit.variable()].neg_watchers;
            }
        }

        fn attachClause(self: *Self, cref: ClauseRef) !void {
            var clause = self.clause_db.borrow(cref);
            var w0 = Watcher(ClauseRef){ .blocker = clause.expr[1], .cref = cref };
            var w1 = Watcher(ClauseRef){ .blocker = clause.expr[0], .cref = cref };

            try self.getLitWatchers(clause.expr[0]).append(w0);
            try self.getLitWatchers(clause.expr[1]).append(w1);
        }

        fn detachClause(self: *Self, cref: ClauseRef) void {
            var clause = self.clause_db.borrow(cref);

            var ws0 = self.getLitWatchers(clause.expr[0]);
            var ws1 = self.getLitWatchers(clause.expr[1]);

            var i: usize = 0;

            while (true) : (i += 1) {
                if (ws0.items[i].cref.equal(cref)) {
                    _ = ws0.swapRemove(i);
                    break;
                }
            }

            i = 0;

            while (true) : (i += 1) {
                if (ws1.items[i].cref.equal(cref)) {
                    _ = ws1.swapRemove(i);
                    break;
                }
            }
        }

        /// init a new solver, call `deinit()` to free it's memory
        pub fn init(pm: ProofManager, allocator: std.mem.Allocator) !Self {
            return Self{
                .clause_db = ClauseDB(Proof).init(allocator),
                .propagation_queue = std.ArrayList(Lit).init(allocator),
                .assignation_queue = std.ArrayList(Lit).init(allocator),
                .final_conflict = std.ArrayList(Lit).init(allocator),
                .variables = std.ArrayList(VarData(ClauseRef, Proof)).init(allocator),
                .vsids = VSIDS.init(allocator),
                .proof_manager = pm,

                .seen = IntSet(Variable, variableToUsize).init(allocator),
                .analyze_result = std.ArrayList(Lit).init(allocator),

                .lbd_stats = try LBDstats.init(allocator),

                .allocator = allocator,
                .is_unsat = null,
                .level = 0,
                .verbose = 0,

                .stats = SolverStats.init(),
            };
        }

        /// remove the `1 - factor` fraction of less usefull learned clauses
        /// and all the link from the solver for these clauses
        pub fn garbadgeCollect(self: *Self, factor: f64) !void {
            self.stats.addGC();

            try self.clause_db.garbadgeCollect(factor);

            if (self.verbose >= 1) {
                std.debug.print("c {}  ", .{@as(usize, @intFromFloat(self.lbd_stats.mean_size))});
                std.debug.print("{}  ", .{self.clause_db.len_learned()});
                self.stats.print(self.progressEstimate());
            }

            for (self.variables.items) |*var_data| {
                var i: usize = 0;

                while (i < var_data.pos_watchers.items.len) {
                    var cref = var_data.pos_watchers.items[i].cref;
                    if (self.clause_db.is_free(cref)) {
                        _ = var_data.pos_watchers.swapRemove(i);
                    } else {
                        i += 1;
                    }
                }

                i = 0;
                while (i < var_data.neg_watchers.items.len) {
                    var cref = var_data.neg_watchers.items[i].cref;
                    if (self.clause_db.is_free(cref)) {
                        _ = var_data.neg_watchers.swapRemove(i);
                    } else {
                        i += 1;
                    }
                }
            }
        }

        /// free all the memory of the solver
        pub fn deinit(self: *Self) void {
            self.propagation_queue.deinit();
            self.assignation_queue.deinit();
            self.final_conflict.deinit();
            self.analyze_result.deinit();
            self.lbd_stats.deinit();
            self.vsids.deinit();

            self.seen.deinit();

            for (self.variables.items) |*var_data| {
                var_data.pos_watchers.deinit();
                var_data.neg_watchers.deinit();
            }

            self.variables.deinit();
            self.clause_db.deinit();
        }

        /// create a new variable and initialize all it's states
        pub fn addVariable(self: *Self) SolverError!u31 {
            var new_var_usize = self.variables.items.len;

            if (new_var_usize != (new_var_usize & ((2 << 31) - 1))) {
                return error.TooManyVariables;
            }

            var new_var: Variable = @truncate(new_var_usize);

            var new_var_data = VarData(ClauseRef, Proof){
                .state = null,
                .pos_watchers = std.ArrayList(Watcher(ClauseRef)).init(self.allocator),
                .neg_watchers = std.ArrayList(Watcher(ClauseRef)).init(self.allocator),
            };

            try self.variables.append(new_var_data);
            try self.vsids.addVariable();

            return new_var;
        }

        pub fn analyze(self: *Self, conf: ClauseRef) ![]Lit {
            self.analyze_result.clearRetainingCapacity();
            self.seen.clear();

            // search the maximum level of assignation of the conflict
            var level: usize = 0;

            for (self.clause_db.borrow(conf).expr) |lit| {
                try std.testing.expect(self.value(lit) == .lfalse);
                var lit_level = self.levelOf(lit.variable());

                if (lit_level > level) level = lit_level;
            }

            try self.analyze_result.append(Lit.init(0, true));
            self.proof_manager.initResolution(self.clause_db.borrow(conf).proof);

            var IP_counter: usize = 0; // number of implication points of the current clause
            var index = self.assignation_queue.items.len - 1;
            var cref: ClauseRef = conf;

            while (true) {
                var clause = self.clause_db.borrow(cref);
                self.clause_db.incrActivity(cref);

                switch (clause.stats) {
                    .Learned => |*lcs| {
                        var lbd = try self.lbd_stats.getLBD(self, clause.expr);
                        if (lbd < lcs.lbd) lcs.lbd = lbd;
                    },
                    else => {},
                }

                for (clause.expr) |lit| {
                    // in this case, `self.reasonOf(lit.variable()) == cref`
                    if (self.value(lit) == .ltrue) continue;

                    if (!self.seen.inSet(lit.variable())) {
                        if (self.levelOf(lit.variable()) > 0) {
                            try self.vsids.incrActivity(lit.variable());

                            if (self.levelOf(lit.variable()) < level) {
                                try self.seen.insert(lit.variable());
                                try self.analyze_result.append(lit);
                            } else {
                                try self.seen.insert(lit.variable());
                                IP_counter += 1;
                            }
                        } else {
                            self.proof_manager.pushResolutionStep(
                                lit.variable(),
                                self.proofOf(lit.variable()).?,
                            );
                        }
                    }
                }

                while (!self.seen.inSet(self.assignation_queue.items[index].variable())) : (index -= 1) {}
                var pivot = self.assignation_queue.items[index];
                self.analyze_result.items[0] = pivot.not();
                self.seen.remove(pivot.variable());
                IP_counter -= 1;

                if (IP_counter == 0) break;

                // `IP_counter > 0` so `pivot` is not the UIP
                cref = self.reasonOf(pivot.variable()).?;
                self.proof_manager.pushResolutionStep(
                    pivot.variable(),
                    self.clause_db.borrow(cref).proof,
                );
            }

            //index = 1;
            //minimize_loop: while (index < self.analyze_result.items.len) {
            //    var v = self.analyze_result.items[index].variable();

            //    var reason = self.reasonOf(v) orelse {
            //        index += 1;
            //        continue;
            //    };

            //    var clause = self.clause_db.borrow(reason);

            //    for (clause.expr) |l| {
            //        if (!self.seen.inSet(l.variable())) {
            //            index += 1;
            //            continue :minimize_loop;
            //        }
            //    }

            //    _ = self.analyze_result.swapRemove(index);
            //}

            return self.analyze_result.items;
        }
    };
}
