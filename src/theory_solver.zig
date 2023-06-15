const std = @import("std");
const Lit = @import("lit.zig").Lit;

pub fn TSolver(comptime Context: type, comptime Err: type) type {
    return struct {
        const Self = @This();

        context: Context,

        /// the returned slice is owned by the theory solver,
        /// `_propagate(ctx, lit, lazy)` return if the theory solver
        /// detect a conflict, if `lazy` is set to  true if all the
        /// variables of the sat solver are assigned
        _propagate: *const fn (Context, Lit, bool) Err!?[]Lit,

        _backtrack: *const fn (Context) Err!void,

        pub fn propagate(self: Self, lit: Lit, lazy: bool) Err!?[]Lit {
            return self._propagate(self.context, lit, lazy);
        }

        pub fn backtrack(self: Self) Err!void {
            return self._backtrack(self.context);
        }
    };
}

/// a minimalistic theory solver for no theory
const MinimalTSolver = struct {
    const Self = @This();

    pub fn backtrack(self: Self) error{}!void {
        _ = self;
    }

    pub fn propagate(self: Self, lit: Lit, lazy: bool) error{}!?[]Lit {
        _ = self;
        _ = lazy;
        _ = lit;

        return null;
    }

    const Solver = TSolver(Self, error{});

    pub fn solver(self: Self) Solver {
        return Solver{
            .context = self,
            ._propagate = propagate,
            ._backtrack = backtrack,
        };
    }
};

test "minimal solver test" {
    var minimal_solver: MinimalTSolver = undefined;
    var solver = minimal_solver.solver();

    _ = try solver.propagate(Lit.init(0, false), false);
    _ = try solver.backtrack();
}
