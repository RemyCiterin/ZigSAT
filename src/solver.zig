pub const std = @import("std");

// main data structure used by the solver
pub const Heap = @import("Heap.zig").Heap;
pub const IntSet = @import("IntSet.zig").IntSet;
pub const IntMap = @import("IntMap.zig").IntMap;

const VSIDS = @import("VSIDS.zig");

const LBDstats = @import("LBDstats.zig");

// representation of literals and possibly undefined boolean
pub const lbool = @import("lit.zig").lbool;
pub const Lit = @import("lit.zig").Lit;

// import clause and clause manager/garbadge collector
const ClauseDB = @import("clause.zig").ClauseDB;
const Clause = @import("clause.zig").Clause;

pub const generateClause = @import("lit.zig").generateClause;

/// when a clause watch a variable (the variable is one of the two
/// first literals of it's expression), we store this clause
/// (to detect efficiently unit propagation) and
/// the other watcher literal (for optimization)
pub fn Watcher(comptime ClauseRef: type) type {
    return struct { cref: ClauseRef, blocker: Lit, binary: bool };
}

pub fn TClause(comptime Proof: type) type {
    return struct {
        expr: []Lit,
        proof: Proof,
    };
}

const Variable = @import("lit.zig").Variable;
pub const variableToUsize = @import("lit.zig").variableToUsize;

pub const SimplifyHeuristic = struct {
    /// simplify every 2000 + 500 * x conflicts
    fuel: usize,

    /// num of previous simplification
    num: usize,

    pub fn init() @This() {
        return .{
            .fuel = 0,
            .num = 0,
        };
    }

    pub fn addConflict(self: *@This()) void {
        if (self.fuel > 0) self.fuel -= 1;
    }

    pub fn addSimplify(self: *@This()) void {
        self.fuel = 1000 + 100 * self.num;
        self.num += 1;
    }

    pub fn maySimplify(self: @This()) bool {
        return self.fuel == 0;
    }
};

pub const SolverStats = struct {
    restart: usize,
    conflict: usize,
    simplify: usize,
    gc: usize,
    prop: usize,

    const Self = @This();

    fn init() Self {
        return Self{
            .simplify = 0,
            .restart = 0,
            .gc = 0,
            .conflict = 0,
            .prop = 0,
        };
    }

    pub fn print(self: Self, progress: f64) void {
        std.debug.print("rst: {}  simp: {}  conf: {}  prop: {}  progress: {d:.4}\n", .{
            self.restart,
            self.simplify,
            self.conflict,
            self.prop,
            progress,
        });
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

    pub fn addSimplify(self: *Self) void {
        self.simplify += 1;
    }

    pub fn numConflict(self: Self) usize {
        return self.conflict;
    }

    pub fn addPropagation(self: *Self) void {
        self.prop += 1;
    }
};

pub fn Solver(comptime ProofManager: type, comptime TSolver: type) type {
    comptime {
        @import("trait.zig").Trait(ProofManager, .{
            .{
                .name = "Proof",
                .type = type,
            },
            .{
                .name = "addAxiom",
                .type = fn (*ProofManager, []Lit) ProofManager.Proof,
            },
            .{
                .name = "initResolution",
                .type = fn (*ProofManager, ProofManager.Proof) void,
            },
            .{
                .name = "pushResolutionStep",
                .type = fn (*ProofManager, Variable, ProofManager.Proof) void,
            },
            .{
                .name = "finalizeResolution",
                .type = fn (*ProofManager) ProofManager.Proof,
            },
        });

        @import("trait.zig").Trait(ProofManager.Proof, .{
            .{
                .name = "deinit",
                .type = fn (ProofManager.Proof) void,
            },
            .{
                .name = "clone",
                .type = fn (ProofManager.Proof) ProofManager.Proof,
            },
        });

        @import("trait.zig").Trait(TSolver, .{
            .{
                .name = "pop",
                .type = fn (*TSolver) void,
                .doc =
                \\`pop` have the effect to pop a backtracking point to the tsolver:
                \\all the assignations since the last call to `push` must be deassigned
                ,
            },
            .{
                .name = "push",
                .type = fn (*TSolver) void,
                .doc =
                \\`push` have the effect of pushing a backtracking point to the theory solver
                ,
            },
            .{
                .name = "assign",
                .type = fn (*TSolver, Lit) void,
                .doc =
                \\assign a value of a literal in the solver, we must use `pop` to unassign it
                ,
            },
            .{
                .name = "weakPropagate",
                .type = fn (*TSolver) ?Lit,
                .doc =
                \\`weakPropagate` take as input a solver state and return
                \\a literal propagated by the theory, in particular if this
                \\literal is true in the current assignment then the SAT
                \\solver will propagate it, and if the literal is false the
                \\SAT solver will raise a theory conflict and backtrack
                ,
            },
            .{
                .name = "reason",
                .type = fn (*TSolver, Variable) TClause(ProofManager.Proof),
                .doc =
                \\`reason(v)` must be called if a previous call to `weakPropagate`
                \\returned `l := Lit.init(v, b)`, in this case the return clause
                \\is the reason for the assignment of `v` and is of the form
                \\`l_1 ... l_n` with `n > 1`, one of `l_i` equal to `l` and
                \\the other assigned to false
                ,
            },
            .{
                .name = "check",
                .type = fn (*TSolver) ?TClause(ProofManager.Proof),
                .doc =
                \\check that the current model is true and return a theory unsat core if not
                ,
            },
        });
    }

    return struct {
        pub const Proof = ProofManager.Proof;
        pub const ClauseRef = ClauseDB(Proof).ClauseRef;

        pub const SmtClause = union(enum) {
            sat: ClauseRef,
            theory: TClause(Proof),

            pub fn expr(self: @This(), db: *ClauseDB(Proof)) []Lit {
                return switch (self) {
                    .sat => |cref| db.borrow(cref).expr,
                    .theory => |c| c.expr,
                };
            }

            pub fn proof(self: @This(), db: *ClauseDB(Proof)) Proof {
                return switch (self) {
                    .sat => |cref| db.borrow(cref).proof.clone(),
                    .theory => |c| c.proof.clone(),
                };
            }

            pub fn incrLock(self: @This(), db: *ClauseDB(Proof)) void {
                switch (self) {
                    .sat => |cref| db.incrLock(cref),
                    else => {},
                }
            }

            pub fn decrLock(self: @This(), db: *ClauseDB(Proof)) void {
                switch (self) {
                    .sat => |cref| db.decrLock(cref),
                    else => {},
                }
            }

            pub fn incrActivity(self: @This(), db: *ClauseDB(Proof)) void {
                switch (self) {
                    .sat => |cref| db.incrActivity(cref),
                    else => {},
                }
            }
        };

        const Reason = union(enum) { Eager: SmtClause, Lazy };
        const AssignStack = @import("assign.zig").AssignStack(Reason, Proof);

        /// all the data of a variable store by the solver
        const VarWatchers = struct {
            /// the list of all the watchers of the literal `Lit.init(variable, true)`
            pos_watchers: std.ArrayList(Watcher(ClauseRef)),

            /// the list of all the watchers of the literal `Lit.init(variable, false)`
            neg_watchers: std.ArrayList(Watcher(ClauseRef)),
        };

        /// buffer of literals to propagate, all the literals in it are also in
        /// `self.assignation_queue`
        propagation_queue: std.ArrayList(Lit),

        /// a ClauseDB for clause allocation and garbadge collection
        clause_db: ClauseDB(Proof),

        /// set of variable watchers
        watchers: std.MultiArrayList(VarWatchers),

        /// use and compute lbd
        lbd_stats: LBDstats,

        /// data structure that contain all the informations about the assignation stack
        stack: AssignStack,

        /// theory solver
        tsolver: TSolver,

        /// an heap for VSIDS heuristic
        vsids: VSIDS,

        /// level of verbosity
        verbose: i32,

        /// allocator of the solver
        allocator: std.mem.Allocator,

        /// if true then the solver state is unsat
        is_unsat: ?Proof,

        /// simplification heuristic
        simplify_h: SimplifyHeuristic = SimplifyHeuristic.init(),

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

        /// unsat core of the last unsatisfiable call to the solver
        unsat_core: std.ArrayList(Lit),

        const Self = @This();
        const SolverError = std.mem.Allocator.Error || error{TooManyVariables};

        /// print the current solving progress of the solver
        pub fn progressEstimate(self: *Self) f64 {
            var progress: f64 = 0.0;
            const F: f64 = 1.0 / @as(f64, @floatFromInt(self.stack.len()));
            var level: usize = 0;

            for (self.stack.view()) |l| {
                if (self.levelOf(l.variable()) != level)
                    level = self.levelOf(l.variable());

                progress += std.math.pow(f64, F, @as(f64, @floatFromInt(level)));
            }

            return progress / @as(f64, @floatFromInt(self.stack.len()));
        }

        /// check if the current model satisfy all the initial clauses
        pub fn checkModel(self: *Self) bool {
            var iter = self.clause_db.iterInitial();
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

        fn theoryPropagate(self: *Self) !?TClause(Proof) {
            while (true) {
                if (self.tsolver.weakPropagate()) |lit| {
                    while (lit.variable() >= self.stack.len())
                        _ = try self.addVariable();

                    if (self.value(lit) == .ltrue) continue;
                    if (self.value(lit) == .lfalse) {
                        var reason = self.tsolver.reason(lit.variable());
                        std.debug.assert(reason.expr.len >= 1);

                        for (reason.expr) |l|
                            std.debug.assert(self.value(l) == .lfalse);

                        return reason;
                    }

                    if (self.level == 0) {
                        var reason = self.tsolver.reason(lit.variable());
                        std.debug.assert(reason.expr.len >= 1);

                        self.proof_manager.initResolution(reason.proof);

                        for (reason.expr) |l| {
                            var v = l.variable();
                            if (v == lit.variable()) {
                                if (!l.equals(lit)) @panic("TSolver error");
                                continue;
                            }
                            if (self.value(l) != .lfalse) @panic("TSolver error");
                            self.proof_manager.pushResolutionStep(v, self.proofOf(v).?);
                        }

                        var proof = self.proof_manager.finalizeResolution();
                        try self.mkAssignation(lit, null, proof, false);
                    } else {
                        try self.mkAssignation(lit, null, null, true);
                    }

                    continue;
                }

                return null;
            }
        }

        /// propagate all the assigned variables and see if their is a conflict
        fn propagate(self: *Self) !?SmtClause {
            while (true) {
                while (self.propagation_queue.items.len > 0) {
                    self.stats.addPropagation();

                    if (try self.propagateLit(self.propagation_queue.pop())) |cref| {
                        return .{ .sat = cref };
                    }
                }

                if (try self.theoryPropagate()) |conf| return .{ .theory = conf };
                if (self.propagation_queue.items.len > 0) continue;

                return null;
            }
        }

        /// use the watcher lists to propagate the assignation of a variable inside the solver
        fn propagateLit(self: *Self, lit: Lit) !?ClauseRef {
            var watchers = self.getLitWatchers(lit.not());

            std.debug.assert(self.value(lit) == .ltrue);

            var i: usize = 0;
            watchers_loop: while (i < watchers.items.len) {
                var blocker: Lit = watchers.items[i].blocker;
                var cref: ClauseRef = watchers.items[i].cref;

                if (self.value(blocker) == .ltrue) {
                    i += 1;
                    continue;
                }

                std.debug.assert(!self.clause_db.isFree(cref));
                var clause = self.clause_db.borrow(cref);

                if (clause.expr[0].equals(lit.not())) {
                    std.mem.swap(Lit, &clause.expr[0], &clause.expr[1]);
                }

                std.debug.assert(lit.not().equals(clause.expr[1]));

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
                            .append(Watcher(ClauseRef){
                            .blocker = blocker,
                            .cref = cref,
                            .binary = clause.expr.len == 2,
                        });
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
                    self.proof_manager.initResolution(clause.proof.clone());

                    for (1..clause.expr.len) |idx| {
                        var v = clause.expr[idx].variable();
                        self.proof_manager.pushResolutionStep(v, self.proofOf(v).?);
                    }

                    proof = self.proof_manager.finalizeResolution();
                }

                try self.mkAssignation(clause.expr[0], if (self.level == 0) null else cref, proof, false);
                i += 1;
            }

            return null;
        }

        /// return the level of assignation of an assigned variable
        /// undefined behaviour if the variable is not assigned
        pub fn levelOf(self: Self, variable: Variable) u32 {
            return self.stack.get(variable, .level).?;
        }

        /// return the level of assignation of an assigned variable
        /// undefined behaviour if the variable is not assigned
        pub fn positionOf(self: Self, variable: Variable) usize {
            return self.stack.get(variable, .position).?;
        }

        /// return the reason of assignation of an assigned variables:
        /// null if the variable is a decision variable of a variable assigned at level 0
        /// undefined behaviour if the variable is not assigned
        /// The index of the implied variable may not be zero
        pub fn reasonOf(self: *Self, variable: Variable) ?SmtClause {
            switch (self.stack.get(variable, .reason) orelse return null) {
                .Eager => |ret| return ret,
                .Lazy => {
                    var reason = self.tsolver.reason(variable);
                    // the reason of assignation of a variables must be of size > 1 and with
                    // all literal negative except for the implied literal
                    std.testing.expect(reason.expr.len >= 2) catch @panic("tsolvre error");
                    var found = false;

                    for (0.., reason.expr) |i, lit| {
                        if (lit.variable() == variable) {
                            std.testing.expect(!found) catch @panic("tsolver error");
                            std.mem.swap(Lit, &reason.expr[0], &reason.expr[i]);
                            found = true;
                        } else {
                            var val = self.value(lit);
                            std.testing.expect(val == .lfalse) catch @panic("tsolver error");
                            //std.testing.expect(
                            //    self.positionOf(lit.variable()) < self.positionOf(variable),
                            //) catch @panic("tsolver error");
                        }
                    }

                    if (reason.expr[0].variable() != variable) @panic("tsolver error");

                    self.stack.updateReason(variable, .{ .Eager = .{ .theory = reason } });
                    return .{ .theory = reason };
                },
            }
        }

        /// return a proof of assignation of an assigned variable, if `self.levelOf(v) == 0`
        /// undefined behaviour if the variable is not assigned
        pub fn proofOf(self: Self, variable: Variable) ?Proof {
            return if (self.stack.get(variable, .proof)) |proof| proof.clone() else null;
        }

        /// return the value of assignation of a literal, `.lundef` if not assigned
        pub fn value(self: Self, lit: Lit) lbool {
            return self.stack.value(lit);
        }

        /// return the value of assignation of a variable
        pub fn valueOf(self: Self, v: Variable) lbool {
            return self.stack.get(v, .value);
        }

        /// iterate over all the proofs in the solver, maybe used for GC
        pub fn iterateProof(self: *Self, f: *const fn (Proof) void) void {
            var iter_learned = self.clause_db.iterLearned();

            while (iter_learned.next()) |cref| {
                f(self.clause_db.borrow(cref).proof);
            }

            var iter_initial = self.clause_db.iterInitial();

            while (iter_initial.next()) |cref| {
                f(self.clause_db.borrow(cref).proof);
            }

            for (self.assign.view()) |lit| {
                var v = lit.variable();

                if (self.stack.get(v, .proof)) |proof|
                    f(proof);

                switch (self.stack.get(v, .reason)) {
                    .Eager => |reason| f(reason.proof),
                    else => {},
                }
            }

            if (self.is_unsat) |proof| f(proof);
        }

        pub fn print(self: *Self) void {
            self.clause_db.printDB();

            std.debug.print("assignation queue\n", .{});
            for (self.stack.view()) |lit| {
                var x: i64 = @intCast(lit.variable());
                var y = if (lit.sign()) x else -x;
                std.debug.print("{} ", .{y});
            }
            std.debug.print("\n", .{});
        }

        /// remove all the literals assigned to `false` of a clause at level `0`,
        /// or remove the clause if it is satisfied at level `0`
        fn simplify_clause(self: *Self, cref: ClauseRef) !void {
            std.debug.assert(self.level == 0);

            var clause = self.clause_db.borrow(cref);

            for (clause.expr) |lit| {
                if (self.value(lit) == .ltrue) {
                    self.detachClause(cref);
                    self.clause_db.free(cref);
                    return;
                }
            }

            self.proof_manager.initResolution(clause.proof);

            var i: usize = 2;
            while (i < clause.expr.len) {
                var lit = clause.expr[i];
                if (self.value(lit) == .lfalse) {
                    self.proof_manager.pushResolutionStep(
                        lit.variable(),
                        self.proofOf(lit.variable()).?,
                    );
                    std.mem.swap(Lit, &clause.expr[i], &clause.expr[clause.expr.len - 1]);
                    clause.expr.len -= 1;
                    continue;
                }

                i += 1;
            }

            clause.proof = self.proof_manager.finalizeResolution();
        }

        pub fn simplify(self: *Self) !void {
            self.simplify_h.addSimplify();
            self.stats.addSimplify();

            std.debug.assert(self.level == 0);

            var learned = self.clause_db.iterLearned();
            while (learned.next()) |cref| {
                try self.simplify_clause(cref);
            }

            var initial = self.clause_db.iterInitial();
            while (initial.next()) |cref| {
                try self.simplify_clause(cref);
            }
        }

        fn addLearnedClause(self: *Self, expr: []const Lit, lbd: usize, proof: Proof) !ClauseRef {
            std.debug.assert(expr.len >= 2);

            var cref = try self.clause_db.initClause(true, expr, proof);
            var clause = self.clause_db.borrow(cref);
            try self.attachClause(cref);
            clause.setLBD(lbd);
            return cref;
        }

        /// the expression is borrow by the caller, the caller must deinit it
        pub fn addClause(self: *Self, expr: *std.ArrayList(Lit)) !void {
            std.debug.assert(self.level == 0);

            for (expr.items) |lit| {
                while (self.stack.len() <= lit.variable())
                    _ = try self.addVariable();
            }

            if (self.is_unsat) |_| {
                // the formula is already unsat
                return;
            }

            if (try generateClause(expr))
                return;

            var proof = self.proof_manager.addAxiom(expr.items);
            self.proof_manager.initResolution(proof);

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
                try self.mkAssignation(expr.items[0], null, proof, false);
                if (try self.propagate()) |conf| {
                    self.proof_manager.initResolution(conf.proof(&self.clause_db));
                    for (conf.expr(&self.clause_db)) |lit| {
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
            var l = self.stack.view().len;

            if (l == 0) return null;
            return self.stack.view()[l - 1];
        }

        fn mkAssignation(self: *Self, lit: Lit, cref: ?ClauseRef, proof: ?Proof, treason: bool) !void {
            if (cref) |c| {
                var clause = self.clause_db.borrow(c);
                for (clause.expr) |l|
                    if (l.variable() != lit.variable())
                        std.debug.assert(self.value(l) == .lfalse);
            }

            std.debug.assert(self.value(lit) == .lundef);

            if (cref) |_| std.debug.assert(self.level > 0);

            try self.propagation_queue.append(lit);

            if (cref != null) {
                self.clause_db.incrLock(cref.?);
            }

            // assign the literal in the variable decision heuristic
            try self.vsids.setState(lit.variable(), lbool.init(lit.sign()));

            // assign the literal in the theory solver
            self.tsolver.assign(lit);

            var reason: ?Reason =
                if (cref) |c| Reason{ .Eager = .{ .sat = c } } else if (treason) Reason{ .Lazy = {} } else null;
            try self.stack.assign(lit, reason, proof);
        }

        fn dequeueAssignation(self: *Self) !Lit {
            var lit = self.stack.lastAssign().?;
            std.debug.assert(self.value(lit) == .ltrue);

            var v = lit.variable();
            std.debug.assert(self.levelOf(v) > 0);
            if (self.stack.get(v, .reason)) |reason| {
                switch (reason) {
                    .Eager => |smt_clause| {
                        switch (smt_clause) {
                            .sat => |cref| self.clause_db.decrLock(cref),
                            .theory => |tclause| {
                                self.allocator.free(tclause.expr);
                                tclause.proof.deinit();
                            },
                        }
                    },
                    else => {},
                }
            } else {
                self.tsolver.pop();
                self.level -= 1;
            }

            try self.vsids.setState(v, .lundef);
            _ = self.stack.pop();

            return lit;
        }

        pub fn restart(self: *Self) !void {
            self.propagation_queue.clearRetainingCapacity();
            self.lbd_stats.clear();
            self.stats.addRestart();
            while (self.lastAssignation()) |lit| {
                if (self.levelOf(lit.variable()) == 0)
                    break;

                _ = try self.dequeueAssignation();
            }
        }

        /// backjump using a learned expression and a proof of it
        fn backjump(self: *Self, learned: []Lit, proof: Proof) !void {
            var lbd = try self.lbd_stats.getLBD(self, learned);
            try self.lbd_stats.append(lbd, learned.len);

            var max_level = self.levelOf(learned[0].variable());

            // search the backtracking levels and index
            var level: usize = 0;
            var ilevel: usize = 0;
            for (0.., learned) |i, lit| {
                var l = self.levelOf(lit.variable());

                if (l >= level and l < max_level) {
                    ilevel = i;
                    level = l;
                }
            }

            // set a variable at backtracking level at index 1
            if (learned.len >= 2) std.mem.swap(Lit, &learned[1], &learned[ilevel]);

            // backjump
            while (self.lastAssignation()) |lit| {
                if (self.levelOf(lit.variable()) <= level)
                    break;

                _ = try self.dequeueAssignation();
            }

            // two case: the clause is of size `1` (direct assign) or `> 1` (use watchers)
            if (learned.len == 1) {
                try self.mkAssignation(learned[0], null, proof, false);
            } else {
                var new_clause = try self.addLearnedClause(learned, lbd, proof);
                try self.mkAssignation(learned[0], new_clause, null, false);
                self.clause_db.incrActivity(new_clause);
            }

            self.clause_db.decayActivity();
            self.vsids.decayActivity();
        }

        /// search for a conflict
        pub fn searchUntilConflict(self: *Self, assumptions: []const Lit, gc_fuel: *isize) !union(enum) {
            conflict: SmtClause,
            SAT,
            UNSAT: Proof,
        } {
            while (true) {
                if (try self.propagate()) |cref| {
                    return .{ .conflict = cref };
                }

                if (self.lbd_stats.needRestart())
                    try self.restart();

                if (gc_fuel.* < 0) {
                    try self.garbadgeCollect(0.5);
                    gc_fuel.* = @intCast(2000 + 300 * self.stats.numGC());
                }

                if (self.level == 0 and self.simplify_h.maySimplify()) try self.simplify();

                var decision: ?Lit = null;

                for (assumptions) |lit| {
                    if (self.value(lit) == .lfalse) {
                        return .{ .UNSAT = try self.analyzeFinal(lit) };
                    }

                    if (self.value(lit) == .lundef) {
                        decision = lit;
                        break;
                    }
                }

                if (decision == null)
                    decision = self.vsids.mkDecision() orelse {
                        if (self.tsolver.check()) |cref| {
                            return .{ .conflict = .{ .theory = cref } };
                        }
                        return .SAT;
                    };

                self.level += 1;
                self.stack.push();
                self.tsolver.push();
                try self.mkAssignation(decision.?, null, null, false);
            }
        }

        pub fn cdcl(self: *Self, assumptions: []const Lit) !?Proof {
            self.unsat_core.clearRetainingCapacity();
            var gc_fuel: isize = 2000;
            try self.restart();

            if (self.simplify_h.maySimplify()) try self.simplify();
            if (self.is_unsat) |proof| return proof;
            while (true) {
                switch (try self.searchUntilConflict(assumptions, &gc_fuel)) {
                    .SAT => return null,
                    .UNSAT => |p| return p,
                    .conflict => |cref| {
                        if (self.level == 0 or cref.expr(&self.clause_db).len == 0) {
                            self.proof_manager.initResolution(cref.proof(&self.clause_db));

                            for (cref.expr(&self.clause_db)) |lit| {
                                self.proof_manager.pushResolutionStep(
                                    lit.variable(),
                                    self.proofOf(lit.variable()).?,
                                );
                            }

                            var out = self.proof_manager.finalizeResolution();
                            self.is_unsat = out;
                            return out;
                        }

                        self.stats.addConflict();
                        self.simplify_h.addConflict();
                        gc_fuel -= 1;

                        var num_assign = self.stack.view().len;
                        try self.lbd_stats.addNumAssign(num_assign);

                        var new_expr = try self.analyze(cref);
                        var proof = self.proof_manager.finalizeResolution();

                        try self.backjump(new_expr, proof);
                    },
                }
            }
        }

        fn getLitWatchers(self: *Self, lit: Lit) *std.ArrayList(Watcher(ClauseRef)) {
            if (lit.sign()) {
                return &self.watchers.items(.pos_watchers)[lit.variable()];
            } else {
                return &self.watchers.items(.neg_watchers)[lit.variable()];
            }
        }

        fn attachClause(self: *Self, cref: ClauseRef) !void {
            var clause = self.clause_db.borrow(cref);
            var binary = clause.expr.len == 2;

            var w0 = Watcher(ClauseRef){
                .blocker = clause.expr[1],
                .cref = cref,
                .binary = binary,
            };

            var w1 = Watcher(ClauseRef){
                .blocker = clause.expr[0],
                .cref = cref,
                .binary = binary,
            };

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

        /// return a view to the current UNSAT core
        pub fn getUnsatCore(self: Self) []const Lit {
            return self.unsat_core.items;
        }

        // return the number of variables in the solver
        pub fn numVar(self: Self) Variable {
            return @intCast(self.stack.len());
        }

        /// init a new solver, call `deinit()` to free it's memory
        pub fn init(pm: ProofManager, tsolver: TSolver, allocator: std.mem.Allocator) !Self {
            return Self{
                .clause_db = ClauseDB(Proof).init(allocator),
                .propagation_queue = std.ArrayList(Lit).init(allocator),
                .watchers = std.MultiArrayList(VarWatchers){},
                .vsids = VSIDS.init(allocator),
                .proof_manager = pm,
                .tsolver = tsolver,

                .seen = IntSet(Variable, variableToUsize).init(allocator),
                .analyze_result = std.ArrayList(Lit).init(allocator),
                .unsat_core = std.ArrayList(Lit).init(allocator),

                .stack = AssignStack.init(allocator),

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

            if (self.verbose >= 1) {
                std.debug.print("c mean_sz: {}  ", .{@as(usize, @intFromFloat(self.lbd_stats.mean_size))});
                std.debug.print("learned: {}  ", .{self.clause_db.lenLearned()});
                self.stats.print(self.progressEstimate());
            }

            try self.clause_db.garbadgeCollect(factor);

            for (self.watchers.items(.pos_watchers)) |*watchers| {
                var i: usize = 0;

                while (i < watchers.items.len) {
                    var cref = watchers.items[i].cref;
                    if (self.clause_db.isFree(cref)) {
                        _ = watchers.swapRemove(i);
                    } else {
                        i += 1;
                    }
                }
            }

            for (self.watchers.items(.neg_watchers)) |*watchers| {
                var i: usize = 0;

                while (i < watchers.items.len) {
                    var cref = watchers.items[i].cref;
                    if (self.clause_db.isFree(cref)) {
                        _ = watchers.swapRemove(i);
                    } else {
                        i += 1;
                    }
                }
            }
        }

        /// free all the memory of the solver
        pub fn deinit(self: *Self) void {
            self.propagation_queue.deinit();
            self.analyze_result.deinit();
            self.unsat_core.deinit();
            self.lbd_stats.deinit();
            self.stack.deinit();
            self.vsids.deinit();

            self.seen.deinit();

            for (self.watchers.items(.pos_watchers)) |*w| {
                w.deinit();
            }

            for (self.watchers.items(.neg_watchers)) |*w| {
                w.deinit();
            }

            self.watchers.deinit(self.allocator);
            self.clause_db.deinit();
        }

        /// create a new variable and initialize all it's states
        pub fn addVariable(self: *Self) SolverError!Variable {
            var new_var_usize = try self.stack.addVariable();

            var new_var: Variable = @truncate(new_var_usize);

            var new_var_watchers = VarWatchers{
                .pos_watchers = std.ArrayList(Watcher(ClauseRef)).init(self.allocator),
                .neg_watchers = std.ArrayList(Watcher(ClauseRef)).init(self.allocator),
            };

            try self.watchers.append(self.allocator, new_var_watchers);
            try self.vsids.addVariable();

            return new_var;
        }

        /// return a conflic clause with exactly one literal at maximum level at index 0
        fn analyze(self: *Self, conf: SmtClause) ![]Lit {
            self.analyze_result.clearRetainingCapacity();
            self.seen.clear();

            // search the maximum level of assignation of the conflict
            var level: usize = 0;

            for (conf.expr(&self.clause_db)) |lit| {
                std.debug.assert(self.value(lit) == .lfalse);
                var lit_level = self.levelOf(lit.variable());

                if (lit_level > level) level = lit_level;
            }

            try self.analyze_result.append(Lit.init(0, true));
            self.proof_manager.initResolution(conf.proof(&self.clause_db));

            var IP_counter: usize = 0; // number of implication points of the current clause
            var index = self.stack.view().len - 1;
            var cref: SmtClause = conf;

            while (true) {
                switch (cref) {
                    .sat => {
                        var clause = self.clause_db.borrow(cref.sat);
                        cref.incrActivity(&self.clause_db);

                        switch (clause.stats) {
                            .Learned => |*lcs| {
                                var lbd = try self.lbd_stats.getLBD(self, clause.expr);
                                if (lbd < lcs.lbd) lcs.lbd = lbd;
                            },
                            else => {},
                        }
                    },
                    else => {},
                }

                for (cref.expr(&self.clause_db)) |lit| {
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

                while (!self.seen.inSet(self.stack.view()[index].variable())) : (index -= 1) {}
                var pivot = self.stack.view()[index];
                self.analyze_result.items[0] = pivot.not();
                self.seen.remove(pivot.variable());
                IP_counter -= 1;

                if (IP_counter == 0) break;

                // `IP_counter > 0` so `pivot` is not the UIP
                cref = self.reasonOf(pivot.variable()).?;
                self.proof_manager.pushResolutionStep(
                    pivot.variable(),
                    cref.proof(&self.clause_db),
                );
            }

            // if Proof is equal to void, then their is no proof generation (it is possible to minimize clauses)
            if (std.meta.eql(Proof, void)) {
                index = 1;
                minimize_loop: while (index < self.analyze_result.items.len) {
                    var v = self.analyze_result.items[index].variable();

                    var reason = self.reasonOf(v) orelse {
                        index += 1;
                        continue;
                    };

                    for (reason.expr(&self.clause_db)) |l| {
                        if (!self.seen.inSet(l.variable())) {
                            index += 1;
                            continue :minimize_loop;
                        }
                    }

                    _ = self.analyze_result.swapRemove(index);
                }
            }

            return self.analyze_result.items;
        }

        /// return a proof of ~S with S a subset of the local assumptions,
        /// and set the unsat_core to the right value
        fn analyzeFinal(self: *Self, lit: Lit) !Proof {
            self.unsat_core.clearRetainingCapacity();
            self.seen.clear();

            try self.unsat_core.append(lit);

            if (self.levelOf(lit.variable()) == 0) {
                return self.proofOf(lit.variable()).?;
            }

            std.debug.assert(self.level > 0);

            try self.seen.insert(lit.variable());

            var index: usize = self.stack.view().len - 1;
            while (true) : (index -= 1) {
                var v = self.stack.view()[index].variable();
                if (self.levelOf(v) == 0) break;

                if (self.seen.inSet(v)) {
                    if (self.reasonOf(v)) |cref| {
                        if (v == lit.variable()) {
                            self.proof_manager.initResolution(
                                cref.proof(&self.clause_db),
                            );
                        } else {
                            self.proof_manager.pushResolutionStep(
                                v,
                                cref.proof(&self.clause_db),
                            );
                        }

                        for (cref.expr(&self.clause_db)) |l| {
                            if (self.levelOf(l.variable()) == 0) {
                                self.proof_manager.pushResolutionStep(
                                    l.variable(),
                                    self.proofOf(l.variable()).?,
                                );
                            } else {
                                try self.seen.insert(l.variable());
                            }
                        }
                    } else {
                        try self.unsat_core.append(self.stack.view()[index].not());
                    }
                }

                if (index == 0) break;
            }

            return self.proof_manager.finalizeResolution();
        }
    };
}
