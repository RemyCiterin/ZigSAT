// This file define a C-api for the SAT solver
const std = @import("std");
const Solver = @import("solver.zig").Solver;
const TClause = @import("solver.zig").TClause;
const Lit = @import("lit.zig").Lit;

fn Lit2usize(lit: Lit) usize {
    var v: usize = lit.variable();
    if (lit.sign()) return 1 + 2 * v;
    return 2 * v;
}

const ISet = @import("IntSet.zig").IntSet(Lit, Lit2usize);

pub const EmptyPM = struct {
    pub const Proof = struct {
        pub fn deinit(_: Proof) void {}

        pub fn clone(_: Proof) Proof {
            return .{};
        }
    };

    const This = @This();

    pub fn addAxiom(this: *This, expr: []Lit) Proof {
        _ = this;
        _ = expr;

        return .{};
    }

    pub fn initResolution(this: *This, proof: Proof) void {
        _ = proof;
        _ = this;
    }

    pub fn borrow(this: *This, proof: Proof) void {
        _ = proof;
        _ = this;
    }

    pub fn pushResolutionStep(this: *This, v: @import("lit.zig").Variable, proof: Proof) void {
        _ = proof;
        _ = this;
        _ = v;
    }

    pub fn finalizeResolution(this: *This) Proof {
        _ = this;

        return .{};
    }
};

const EmptyTS = struct {
    const Self = @This();

    pub fn pop(_: *Self) void {}

    pub fn push(_: *Self) void {}

    pub fn assign(_: *Self, _: Lit) void {}

    pub fn weakPropagate(_: *Self) ?Lit {
        return null;
    }

    pub fn reason(_: *Self, _: @import("lit.zig").Variable) TClause(EmptyPM.Proof) {
        unreachable;
    }

    pub fn check(_: *Self) ?TClause(EmptyPM.Proof) {
        return null;
    }
};

const allocator = std.heap.c_allocator;

const State = struct {
    const S = Solver(EmptyPM, EmptyTS);

    clause: std.ArrayList(Lit),
    assumptions: std.ArrayListUnmanaged(Lit) = .{},
    core: ISet,
    solver: S,

    pub fn init() !State {
        return State{
            .clause = std.ArrayList(Lit).init(allocator),
            .solver = try S.init(.{}, .{}, allocator),
            .core = ISet.init(allocator),
        };
    }

    pub fn deinit(self: *State) void {
        std.debug.print("deinit solver\n", .{});
        self.assumptions.deinit(allocator);
        self.clause.deinit();
        self.solver.deinit();
        self.core.deinit();
    }

    pub fn add(self: *State, lit_opt: ?Lit) !void {
        if (lit_opt) |lit| {
            while (self.solver.numVar() <= lit.val)
                _ = try self.solver.addVariable();
            try self.clause.append(lit);
            std.debug.print("add lit with len {}\n", .{self.clause.items.len});
        } else {
            std.debug.print("add clause {}\n", .{self.clause.items.len});
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
        std.debug.print("len: {}, vars: {}\n", .{
            self.clause.items.len,
            self.solver.numVar(),
        });
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
    std.debug.print("add lit: {}\n", .{lit});
    if (lit == 0)
        return state.add(null) catch unreachable;

    var s: bool = lit > 0;
    var v: u31 = @intCast(if (s) lit else -lit);

    state.add(Lit.init(v, s)) catch unreachable;
}

/// assume a literal for the next solve
pub export fn zigsat_assume(state: *State, lit: i32) callconv(.C) void {
    var s: bool = lit > 0;
    var v: u31 = @intCast(if (s) lit else -lit);

    state.assume(Lit.init(v, s)) catch unreachable;
}

/// return 1 if a literal is into the unsat-core, 0 otherwise
pub export fn zigsat_failed(state: *State, lit: i32) callconv(.C) u8 {
    var s: bool = lit > 0;
    var v: u31 = @intCast(if (s) lit else -lit);

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
    var v: u31 = @intCast(if (s) lit else -lit);

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
