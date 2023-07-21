const std = @import("std");
const Lit = @import("lit.zig").Lit;

/// a minimalistic theory solver for no theory
const MinimalTSolver = struct {
    const Self = @This();

    /// a type of proof, in this case, no theory are supported, so the
    /// type of proof is empty
    const TProof = enum {};

    /// a type of ast for theory terms, usualy the theory solver
    /// communicate with a kind of term manager
    const AST = void;

    /// backtrack the last assignation
    pub fn backtrack(self: *Self) error{}!void {
        _ = self;
    }

    pub fn addVariable(self: *Self, ast: AST) error{}!void {
        _ = self;
        _ = ast;
    }

    /// `propagate(self, lit, lazy)` propagate the literal assignation to it's internal
    /// data structures, if lazy is set to true then the solver may perform it's
    /// propagation latter
    pub fn propagate(self: *Self, lit: Lit, lazy: bool) error{}!?[]Lit {
        _ = self;
        _ = lazy;
        _ = lit;

        return null;
    }

    // return the reason of the last theory conflict
    pub fn reason(self: *Self) TProof {
        _ = self;
    }
};

test "minimal solver test" {
    var solver: MinimalTSolver = undefined;
    try solver.addVariable({});

    _ = try solver.propagate(Lit.init(0, false), false);
    _ = try solver.backtrack();
}
