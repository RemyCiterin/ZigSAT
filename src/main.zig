const std = @import("std");
const Solver = @import("solver.zig").Solver;
const TClause = @import("solver.zig").TClause;
const Lit = @import("lit.zig").Lit;

pub const EmptyPM = struct {
    pub const Proof = void;

    const This = @This();

    pub fn addAxiom(this: *This, expr: []Lit) void {
        _ = this;
        _ = expr;
    }

    pub fn initResolution(this: *This, proof: void) void {
        _ = proof;
        _ = this;
    }

    pub fn borrow(this: *This, proof: void) void {
        _ = proof;
        _ = this;
    }

    pub fn release(this: *This, proof: void) void {
        _ = proof;
        _ = this;
    }

    pub fn pushResolutionStep(this: *This, v: @import("lit.zig").Variable, proof: void) void {
        _ = proof;
        _ = this;
        _ = v;
    }

    pub fn finalizeResolution(this: *This) void {
        _ = this;
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

    pub fn reason(_: *Self, _: @import("lit.zig").Variable) TClause(void) {
        unreachable;
    }

    pub fn check(_: *Self) ?TClause(void) {
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
    solver.verbose = 1;
    //defer solver.deinit();

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

    const assumptions: [0]Lit = undefined;
    var b = try solver.cdcl(assumptions[0..]);

    std.debug.print("c ", .{});
    solver.stats.print(solver.progressEstimate());
    if (b == null) try std.testing.expect(solver.checkModel());
    std.debug.print("s {s}\n", .{if (b == null) "SAT" else "UNSAT"});
}
