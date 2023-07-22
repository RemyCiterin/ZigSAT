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

    //try solver.parse(buffer);
    var cnf = std.ArrayList([]Lit).init(allocator);
    defer {
        for (cnf.items) |expr_to_free|
            allocator.free(expr_to_free);

        cnf.deinit();
    }

    var max_var = try @import("parse.zig").parseDIMACS(allocator, buffer, &cnf);

    i = 0;
    while (i <= max_var) : (i += 1) {
        _ = try solver.addVariable();
    }

    for (cnf.items) |expr_to_add| {
        try solver.addClause(expr_to_add);
    }

    solver.verbose = 1;
    const assumptions: [0]Lit = undefined;
    var b = try solver.cdcl(assumptions[0..]);
    solver.stats.print(solver.progressEstimate());
    if (b == null) try std.testing.expect(solver.checkModel());
    std.debug.print("{}\n", .{b == null});
}

test "random clause manager test" {
    //var rnd = std.rand.DefaultPrng.init(0);
    const ProofManager = @import("proof_manager.zig").EmptyProofManager;

    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        _ = gpa.deinit();
    }

    var expr = std.ArrayList(Lit).init(allocator);
    defer expr.deinit();

    const iter_dir = try std.fs.cwd().openIterableDir("tests_competition", .{});
    std.debug.print("\n", .{});

    var iter = iter_dir.iterate();
    var index: usize = 0;

    while (try iter.next()) |entry| : (index += 1) {
        if (entry.kind == .File) {
            var solver = try Solver(ProofManager).init(allocator);
            defer solver.deinit();
            solver.verbose = 1;

            const file_path =
                try std.fmt.allocPrint(allocator, "tests_competition/{s}", .{entry.name});
            std.debug.print("{s}\n", .{file_path});
            defer allocator.free(file_path);

            const file = try std.fs.cwd().openFile(file_path, .{});
            defer file.close();

            const file_size = try file.getEndPos();

            var buffer = try allocator.alloc(u8, file_size);
            defer allocator.free(buffer);

            var bytes_read = try file.read(buffer);

            try std.testing.expect(bytes_read == buffer.len);

            var cnf = std.ArrayList([]Lit).init(allocator);
            defer {
                for (cnf.items) |expr_to_free|
                    allocator.free(expr_to_free);

                cnf.deinit();
            }

            var max_var = try @import("parse.zig").parseDIMACS(allocator, buffer, &cnf);

            var i: usize = 0;
            while (i <= max_var) : (i += 1) {
                _ = try solver.addVariable();
            }

            for (cnf.items) |expr_to_add| {
                try solver.addClause(expr_to_add);
            }

            // try solver.parse(buffer);

            const assumptions: [0]Lit = undefined;

            var b = try solver.cdcl(assumptions[0..]);

            std.debug.print("{}\n", .{b == null});
            if (b == null) {
                try std.testing.expect(solver.checkModel());
            }

            if (b != null) {
                const result = try std.ChildProcess.exec(.{
                    .allocator = std.heap.page_allocator,
                    .argv = &[_][]const u8{
                        "z3",
                        file_path,
                    },
                });
                std.debug.print("{s}\n", .{result.stdout});
            }
        }
    }
}
