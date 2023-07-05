const std = @import("std");
const Lit = @import("lit.zig").Lit;
const Variable = @import("lit.zig").Variable;
const lbool = @import("lit.zig").lbool;

const generateClause = @import("lit.zig").generateClause;

pub const Axiom = struct {
    expr: []Lit,
};

/// a resolution chain is a list of resolution step apply to a base proof
pub const Resolution = struct {
    pub const ResStep = struct { variable: Variable, proof: ProofRef };

    /// base of the resolution chain
    base: ProofRef,

    /// list of step of the resolution chain
    steps: []ResStep,

    /// reference to it's valid representation in memory, usefull for garbadge collection
    pref: ProofRef,

    /// expression value for proof checking
    expr: ?[]Lit = null,

    /// if true: keep the proof a the next garbadge collection step
    keep: bool = false,
};

pub const Proof = union(enum) {
    axiom: Axiom,
    resolution: Resolution,

    const Self = @This();
    pub fn newAddr(self: Self) ?ProofRef {
        switch (self) {
            .resolution => |res| return res.pref,
            else => return null,
        }
    }

    fn updateAddr(self: *Self, addr: ProofRef) void {
        switch (self.*) {
            .resolution => |*res| res.pref = addr,
            else => @panic("cannot update the reference to an axiom"),
        }
    }

    fn setKeepTrue(self: *Self) void {
        switch (self.*) {
            .resolution => |*res| {
                if (res.keep) return;
                res.keep = true;

                res.base.setKeepTrue();
                for (res.steps) |step|
                    step.proof.setKeepTrue();
            },
            else => {},
        }
    }
};

pub const ProofRef = *Proof;

/// this proof manager is the internal proof manager of the solver
pub const ProofManager = struct {
    /// main allocator of the proof manager,
    /// used for axioms and main arrays/lists of the proof manager
    allocator: std.mem.Allocator,

    /// main arena allocator of the solver, used for resolutions chains
    main_arena: std.heap.ArenaAllocator,

    /// transition arena allocator
    transition_arena: std.heap.ArenaAllocator,

    /// set of axioms of the solver
    axioms: std.ArrayList(ProofRef),

    /// set of resolution chains of the solver
    resolutions: std.ArrayList(ProofRef),

    /// base of the next resolution returned by the proof manager
    local_base: ?ProofRef,

    /// set of resolution steps used to resolve the current base
    local_steps: std.ArrayList(Resolution.ResStep),

    /// data structure used to apply the resolutions
    local_expr: std.ArrayList(Lit),

    copy_expr: std.ArrayList(Lit),

    const Self = @This();
    pub const ProofType = ProofRef;
    pub const GenProof = true;

    pub fn getExpr(self: *Self, proof: ProofRef) ?[]const Lit {
        _ = self;

        switch (proof.*) {
            .axiom => |axiom| return axiom.expr,
            .resolution => |state| return state.expr,
        }
    }

    pub fn setExpr(self: *Self, proof: ProofRef) !void {
        if (self.getExpr(proof)) |_| {
            return;
        }

        var state = &proof.resolution;

        try self.setExpr(state.base);
        for (state.steps) |step| {
            try self.setExpr(step.proof);
        }

        self.local_expr.clearRetainingCapacity();
        for (self.getExpr(state.base).?) |lit| {
            try self.local_expr.append(lit);
        }

        for (state.steps) |step| {
            var seen: ?Lit = null;

            var index: usize = 0;
            while (index < self.local_expr.items.len) {
                if (self.local_expr.items[index].variable() == step.variable) {
                    try std.testing.expect(seen == null);
                    seen = self.local_expr.items[index];

                    _ = self.local_expr.swapRemove(index);
                } else {
                    index += 1;
                }
            }

            try std.testing.expect(seen != null);

            for (self.getExpr(step.proof).?) |lit| {
                if (lit.variable() != step.variable) {
                    try self.local_expr.append(lit);
                } else {
                    try std.testing.expect(seen != null and seen.?.not().equals(lit));
                    seen = null;
                }
            }

            try std.testing.expect(seen == null);

            self.copy_expr.clearRetainingCapacity();
            for (self.local_expr.items) |lit| {
                try self.copy_expr.append(lit);
            }
            _ = try generateClause(&self.local_expr, self.copy_expr.items);
        }

        var expr = try self.main_arena.allocator().alloc(Lit, self.local_expr.items.len);
        std.mem.copy(Lit, expr, self.local_expr.items);
        proof.resolution.expr = expr;
    }

    pub fn clear(self: *Self) void {
        self.local_base = null;
        self.local_steps.clearRetainingCapacity();
    }

    pub fn pushStep(self: *Self, variable: Variable, proof: ProofRef) !void {
        try self.local_steps.append(.{ .proof = proof, .variable = variable });
    }

    pub fn setBase(self: *Self, base: ProofRef) void {
        self.clear();
        self.local_base = base;
    }

    pub fn initWithLocalState(self: *Self) !ProofRef {
        if (self.local_steps.items.len == 0)
            return self.local_base.?;

        var allocator = self.main_arena.allocator();

        var steps = try allocator.alloc(Resolution.ResStep, self.local_steps.items.len);
        std.mem.copy(Resolution.ResStep, steps, self.local_steps.items);

        var proof = try allocator.create(Proof);

        proof.* = .{
            .resolution = .{
                .steps = steps,
                .base = self.local_base.?,
                .pref = proof,
                .expr = null,
            },
        };

        try self.resolutions.append(proof);
        //try self.setExpr(proof);

        return proof;
    }

    pub fn initAxiom(self: *Self, expr: []const Lit) !ProofRef {
        var proof = try self.allocator.create(Proof);

        var new_expr = try self.allocator.alloc(Lit, expr.len);
        std.mem.copy(Lit, new_expr, expr);

        proof.* = .{ .axiom = .{ .expr = new_expr } };
        try self.axioms.append(proof);

        return proof;
    }

    pub fn keep(self: *Self, proof: ProofRef) void {
        proof.setKeepTrue();
        _ = self;
    }

    pub fn newAddr(self: *Self, proof: ProofRef) ProofRef {
        _ = self;

        if (proof.newAddr()) |p| {
            return p;
        }
        return proof;
    }

    pub fn init(allocator: std.mem.Allocator) Self {
        var self: Self = undefined;

        self.local_base = null;

        self.local_steps = std.ArrayList(Resolution.ResStep).init(allocator);

        self.allocator = allocator;
        self.main_arena = std.heap.ArenaAllocator.init(allocator);
        self.transition_arena = std.heap.ArenaAllocator.init(allocator);

        self.axioms = std.ArrayList(ProofRef).init(allocator);
        self.resolutions = std.ArrayList(ProofRef).init(allocator);

        self.local_expr = std.ArrayList(Lit).init(allocator);
        self.copy_expr = std.ArrayList(Lit).init(allocator);

        return self;
    }

    pub fn deinit(self: *Self) void {
        self.local_expr.deinit();
        self.copy_expr.deinit();
        self.main_arena.deinit();
        self.transition_arena.deinit();

        for (self.axioms.items) |axiom| {
            self.allocator.free(axiom.axiom.expr);
            self.allocator.destroy(axiom);
        }

        self.axioms.deinit();
        self.resolutions.deinit();
        self.local_steps.deinit();
    }

    /// initialize the garbadge collection:
    /// copy proofs with the keep flag set to true to the transition allocator,
    /// update self reference of proofs
    pub fn garbadgeCollect(self: *Self) !void {
        var allocator = self.transition_arena.allocator();

        var index: usize = 0;

        while (index < self.resolutions.items.len) {
            var proof = self.resolutions.items[index];

            if (proof.resolution.keep) {
                var new_steps = try allocator.alloc(Resolution.ResStep, proof.resolution.steps.len);
                std.mem.copy(Resolution.ResStep, new_steps, proof.resolution.steps);

                proof.resolution.steps = new_steps;
                //proof.resolution.expr = null;

                if (proof.resolution.expr) |expr| {
                    var new_expr = try allocator.alloc(Lit, expr.len);
                    std.mem.copy(Lit, new_expr, expr);
                    proof.resolution.expr = new_expr;
                }

                var new_proof = try allocator.create(Proof);
                proof.updateAddr(new_proof);
                new_proof.* = proof.*;

                self.resolutions.items[index] = new_proof;
                index += 1;
            } else {
                _ = self.resolutions.swapRemove(index);
            }
        }

        for (self.resolutions.items) |proof| {
            proof.resolution.base = self.newAddr(proof.resolution.base);
            for (proof.resolution.steps) |*step| {
                step.proof = self.newAddr(step.proof);
            }
            proof.resolution.keep = false;
        }
    }

    pub fn applyGC(self: *Self) void {
        self.main_arena.deinit();
        self.main_arena = self.transition_arena;
        self.main_arena = std.heap.ArenaAllocator.init(self.allocator);
    }
};

pub const EmptyProofManager = struct {
    pub const ProofType = void;
    pub const GenProof = false;

    const Self = @This();

    pub fn clear(self: *Self) void {
        _ = self;
    }

    pub fn pushStep(self: *Self, v: Variable, proof: ProofType) !void {
        _ = proof;
        _ = self;
        _ = v;
    }

    pub fn setBase(self: *Self, base: ProofType) void {
        _ = base;
        _ = self;
    }

    pub fn initWithLocalState(self: *Self) !ProofType {
        _ = self;
    }

    pub fn initAxiom(self: *Self, expr: []const Lit) !ProofType {
        _ = self;
        _ = expr;
        return {};
    }

    pub fn keep(self: *Self, proof: ProofType) void {
        _ = proof;
        _ = self;
    }

    pub fn newAddr(self: *Self, proof: ProofType) ProofType {
        _ = self;
        return proof;
    }

    pub fn init(allocator: std.mem.Allocator) Self {
        _ = allocator;
        return .{};
    }

    pub fn deinit(self: *Self) void {
        _ = self;
    }

    pub fn garbadgeCollect(self: *Self) !void {
        _ = self;
    }

    pub fn applyGC(self: *Self) void {
        _ = self;
    }
};
