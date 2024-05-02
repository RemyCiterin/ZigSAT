// This file define a C-api for the SAT solver
const std = @import("std");
const Solver = @import("solver.zig").Solver;
const TClause = @import("solver.zig").TClause;
const Variable = @import("lit.zig").Variable;
const Lit = @import("lit.zig").Lit;

fn Lit2usize(lit: Lit) usize {
    var v: usize = lit.variable();
    if (lit.sign()) return 1 + 2 * v;
    return 2 * v;
}

fn Lit2i32(lit: Lit) i32 {
    var v: i32 = @intCast(lit.variable());
    return if (lit.sign()) v else -v;
}

const ISet = @import("IntSet.zig").IntSet(Lit, Lit2usize);

/// a proof manager managed with C types
pub const OpaquePM = struct {
    pub const Proof = extern struct {
        _ptr: *anyopaque,
        _deinit: *const fn (*anyopaque) void,
        _clone: *const fn (*anyopaque) *anyopaque,

        pub fn deinit(proof: Proof) void {
            proof._deinit(proof._ptr);
        }

        pub fn clone(proof: Proof) Proof {
            return .{
                ._ptr = proof._clone(proof._ptr),
                ._deinit = proof._deinit,
                ._clone = proof._clone,
            };
        }
    };

    /// a global state
    _state: *anyopaque,

    /// a C function to free a proof
    _deinit: *const fn (*anyopaque) void,

    /// a C function to clone a proof
    _clone: *const fn (*anyopaque) *anyopaque,

    /// a C function to initialize a resolution using a state and a proof
    _init_resolution: *const fn (*anyopaque, *anyopaque) void,

    /// a C function to push a resolution step using a state, a variable (as a u32) and a proof
    _push_resolution: *const fn (*anyopaque, u32, *anyopaque) void,

    /// a C function to finalize a resolution, returning a proof
    _finalize_resolution: *const fn (*anyopaque) *anyopaque,

    /// add a new axiom and return a proof
    _add_axiom: *const fn (*anyopaque, [*]i32) *anyopaque,

    /// a set of literals used for the interaction with the api
    vector: std.ArrayList(i32),

    const Self = @This();

    pub fn addAxiom(self: *Self, expr: []Lit) Proof {
        self.vector.clearRetainingCapacity();

        for (expr) |l| self.vector.append(Lit2i32(l)) catch unreachable;
        self.vector.append(0) catch unreachable;

        var ptr = self._add_axiom(self._state, @as([*]i32, @ptrCast(self.vector.items[0..])));

        return .{ ._deinit = self._deinit, ._clone = self._clone, ._ptr = ptr };
    }

    pub fn initResolution(self: *Self, proof: Proof) void {
        self._init_resolution(self._state, proof._ptr);
    }

    pub fn pushResolutionStep(self: *Self, variable: Variable, proof: Proof) void {
        self._push_resolution(self._state, @intCast(variable), proof._ptr);
    }

    pub fn finalizeResolution(self: *Self) Proof {
        return .{
            ._ptr = self._finalize_resolution(self._state),
            ._deinit = self._deinit,
            ._clone = self._clone,
        };
    }
};

/// a wrapper for a proof manager with C types that allow using the solver without proof generation
pub const OpaquePMOpt = struct {
    proof_manager: ?OpaquePM,

    pub const Proof = struct {
        proof: ?OpaquePM.Proof,

        pub fn deinit(self: Proof) void {
            if (self.proof) |p|
                p.deinit();
        }

        pub fn clone(self: Proof) Proof {
            if (self.proof) |p|
                return .{ .proof = p.clone() };
            return .{ .proof = null };
        }
    };

    pub fn addAxiom(self: *@This(), axiom: []Lit) Proof {
        if (self.proof_manager) |*pm|
            return .{ .proof = pm.addAxiom(axiom) };
        return .{ .proof = null };
    }

    pub fn initResolution(self: *@This(), proof: Proof) void {
        if (self.proof_manager) |*pm|
            pm.initResolution(proof.proof.?);
    }

    pub fn pushResolutionStep(self: *@This(), v: Variable, proof: Proof) void {
        if (self.proof_manager) |*pm|
            pm.pushResolutionStep(v, proof.proof.?);
    }

    pub fn finalizeResolution(self: *@This()) Proof {
        if (self.proof_manager) |*pm|
            return .{ .proof = pm.finalizeResolution() };
        return .{ .proof = null };
    }
};

/// Definition of a minimal theory solver
const EmptyTS = struct {
    const Self = @This();

    pub fn pop(_: *Self) void {}

    pub fn push(_: *Self) void {}

    pub fn assign(_: *Self, _: Lit) void {}

    pub fn weakPropagate(_: *Self) ?Lit {
        return null;
    }

    pub fn reason(_: *Self, _: @import("lit.zig").Variable) TClause(OpaquePMOpt.Proof) {
        unreachable;
    }

    pub fn check(_: *Self) ?TClause(OpaquePMOpt.Proof) {
        return null;
    }
};

const allocator = std.heap.c_allocator;

/// definition of the internal solver state
const State = struct {
    const S = Solver(OpaquePMOpt, EmptyTS);

    clause: std.ArrayList(Lit),
    assumptions: std.ArrayListUnmanaged(Lit) = .{},
    core: ISet,
    solver: S,

    pub fn init() !State {
        return State{
            .clause = std.ArrayList(Lit).init(allocator),
            .solver = try S.init(.{ .proof_manager = null }, .{}, allocator),
            .core = ISet.init(allocator),
        };
    }

    pub fn deinit(self: *State) void {
        self.assumptions.deinit(allocator);
        self.clause.deinit();
        self.solver.deinit();
        self.core.deinit();
    }

    pub fn add(self: *State, lit_opt: ?Lit) !void {
        if (lit_opt) |lit| {
            while (self.solver.numVar() <= lit.variable())
                _ = try self.solver.addVariable();
            try self.clause.append(lit);
        } else {
            try self.solver.addClause(&self.clause);
            self.clause.clearRetainingCapacity();
        }
    }

    pub fn assume(self: *State, lit: Lit) !void {
        try self.assumptions.append(allocator, lit);
    }

    pub fn failed(self: *State, lit: Lit) bool {
        return self.core.inSet(lit);
    }

    pub fn solve(self: *State) !bool {
        if (self.clause.items.len != 0) @panic("unreachable");
        self.core.clear();

        var result = try self.solver.cdcl(self.assumptions.items);
        self.assumptions.clearRetainingCapacity();

        if (result != null) {
            var core = self.solver.getUnsatCore();
            for (core) |lit| {
                try self.core.insert(lit);
            }

            return false;
        }

        return true;
    }
};

/// initialize the solver
pub export fn zigsat_init() callconv(.C) *State {
    var state = allocator.create(State) catch unreachable;
    state.* = State.init() catch unreachable;
    return state;
}

/// destroy the solver
pub export fn zigsat_release(state: *State) callconv(.C) void {
    state.deinit();
    allocator.destroy(state);
}

/// add a literal into the current clause, add 0 will flush the clause to the solver
pub export fn zigsat_add(state: *State, lit: i32) callconv(.C) void {
    if (lit == 0)
        return state.add(null) catch unreachable;

    var s: bool = lit > 0;
    var v: Variable = @intCast(if (s) lit else -lit);

    state.add(Lit.init(v, s)) catch unreachable;
}

/// assume a literal for the next solve
pub export fn zigsat_assume(state: *State, lit: i32) callconv(.C) void {
    var s: bool = lit > 0;
    var v: Variable = @intCast(if (s) lit else -lit);

    state.assume(Lit.init(v, s)) catch unreachable;
}

/// return 1 if a literal is into the unsat-core, 0 otherwise
pub export fn zigsat_failed(state: *State, lit: i32) callconv(.C) u8 {
    var s: bool = lit > 0;
    var v: Variable = @intCast(if (s) lit else -lit);

    if (state.failed(Lit.init(v, s))) return 1 else return 0;
}

/// solve the system, return 1 if SAT, 0 otherwise
pub export fn zigsat_solve(state: *State) callconv(.C) u8 {
    var result = state.solve() catch unreachable;
    if (result) return 1 else return 0;
}

/// return if a literal is true or false into the current assignation:
/// 0 if unassigned, 1 if true, -1 if false
pub export fn zigsat_value(state: *State, lit: i32) callconv(.C) i32 {
    var s: bool = lit > 0;
    var v: Variable = @intCast(if (s) lit else -lit);

    return switch (state.solver.value(Lit.init(v, s))) {
        .lfalse => -1,
        .ltrue => 1,
        else => 0,
    };
}

/// restart the solver, force it to be at level zero
pub export fn zigsat_restart(state: *State) callconv(.C) void {
    state.solver.restart() catch unreachable;
}

/// simplify the solver state
pub export fn zigsat_simplify(state: *State) callconv(.C) void {
    state.solver.simplify() catch unreachable;
}
