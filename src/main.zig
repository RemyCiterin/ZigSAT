const std = @import("std");
pub const Solver = @import("solver.zig").Solver;
const TClause = @import("solver.zig").TClause;
const Lit = @import("lit.zig").Lit;

var num_proof: isize = 0;

pub const EmptyPM = struct {
    pub const Proof = struct {
        pub fn deinit(_: Proof) void {
            num_proof -= 1;
        }

        pub fn clone(_: Proof) Proof {
            num_proof += 1;
            return .{};
        }
    };

    const This = @This();

    pub fn addAxiom(this: *This, expr: []Lit) Proof {
        _ = this;
        _ = expr;

        num_proof += 1;

        return .{};
    }

    pub fn initResolution(this: *This, proof: Proof) void {
        num_proof -= 1;
        _ = proof;
        _ = this;
    }

    pub fn borrow(this: *This, proof: Proof) void {
        _ = proof;
        _ = this;

        unreachable;
    }

    pub fn pushResolutionStep(this: *This, v: @import("lit.zig").Variable, proof: Proof) void {
        _ = proof;
        _ = this;
        _ = v;

        num_proof -= 1;
    }

    pub fn finalizeResolution(this: *This) Proof {
        _ = this;
        num_proof += 1;

        return .{};
    }
};

pub const EmptyTSolver = struct {
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

pub fn main() !void {
    //var gpa = std.heap.GeneralPurposeAllocator(.{ .safety = false }){};
    //const allocator = gpa.allocator();
    //defer {
    //    _ = gpa.deinit();
    //}
    var allocator = std.heap.c_allocator;
    //var arena = std.heap.ArenaAllocator.init(main_allocator);
    //defer arena.deinit();
    //var allocator = arena.allocator();

    const ProofManager = EmptyPM;
    var solver = try Solver(ProofManager, EmptyTSolver).init(.{}, .{}, allocator);
    defer {
        solver.deinit();
    }
    solver.verbose = 1;

    var file_path = std.ArrayList(u8).init(allocator);

    var i: usize = 0;
    while (std.os.argv[1][i] != 0) : (i += 1)
        try file_path.append(std.os.argv[1][i]);

    //const file_path =
    //    try std.fmt.allocPrint(allocator, "test.cnf", .{});
    std.debug.print("c start parsing {s}\n", .{file_path.items});
    defer file_path.deinit();

    const file = try std.fs.cwd().openFile(file_path.items, .{});
    defer file.close();

    const file_size = try file.getEndPos();

    var buffer = try allocator.alloc(u8, file_size);
    defer allocator.free(buffer);

    var bytes_read = try file.read(buffer);

    try std.testing.expect(bytes_read == buffer.len);

    try @import("parse.zig").parse(&solver, buffer);
    std.debug.print("c start resolution {s}\n", .{file_path.items});

    var assumptions = std.ArrayList(Lit).init(allocator);
    defer assumptions.deinit();
    var b = try solver.cdcl(assumptions.items);

    std.debug.print("c ", .{});
    solver.stats.print(solver.progressEstimate());
    if (b == null) try std.testing.expect(solver.checkModel());
    std.debug.print("s {s}\n", .{if (b == null) "SAT" else "UNSAT"});
}
