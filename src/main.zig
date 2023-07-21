const std = @import("std");
const Solver = @import("solver.zig").Solver;
const Lit = @import("lit.zig").Lit;

pub fn main() !void {
    //var gpa = std.heap.GeneralPurposeAllocator(.{ .safety = false }){};
    //const allocator = gpa.allocator();
    //defer {
    //    _ = gpa.deinit();
    //}
    var allocator = std.heap.c_allocator;

    var expr = std.ArrayList(Lit).init(allocator);
    defer expr.deinit();

    const ProofManager = @import("proof_manager.zig").EmptyProofManager;

    var solver = try Solver(ProofManager).init(allocator);
    defer solver.deinit();

    var file_path = std.ArrayList(u8).init(allocator);

    var i: usize = 0;
    while (std.os.argv[1][i] != 0) : (i += 1)
        try file_path.append(std.os.argv[1][i]);

    //const file_path =
    //    try std.fmt.allocPrint(allocator, "test.cnf", .{});
    std.debug.print("{s}\n", .{file_path.items});
    defer file_path.deinit();

    const file = try std.fs.cwd().openFile(file_path.items, .{});
    defer file.close();

    const file_size = try file.getEndPos();

    var buffer = try allocator.alloc(u8, file_size);
    defer allocator.free(buffer);

    var bytes_read = try file.read(buffer);

    try std.testing.expect(bytes_read == buffer.len);

    try solver.parse(buffer);

    solver.verbose = 1;
    const assumptions: [0]Lit = undefined;
    var b = try solver.cdcl(assumptions[0..]);
    solver.stats.print(solver.progressEstimate());
    if (b == null) try std.testing.expect(solver.checkModel());
    std.debug.print("{}\n", .{b == null});
}
