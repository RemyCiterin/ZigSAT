//! this file define some parser combinator to parse dimacs file
const std = @import("std");
const Lit = @import("lit.zig").Lit;
const lbool = @import("lit.zig").lbool;
const Solver = @import("solver.zig").Solver;

pub fn parse(self: anytype, text: []u8) !void {
    var index: usize = 0;

    const IntParser = struct {
        index: usize,
        text: []u8,

        fn parseInternal(state: *@This()) ?i64 {
            var x: i64 = 0;

            while (true) {
                if (state.index >= state.text.len) return x;
                var char = state.text[state.index];
                switch (char) {
                    '0'...'9' => {
                        var y = char - '0';
                        x = x * 10 + y;
                        state.index += 1;
                    },
                    ' ', '\n', '\t' => return x,
                    else => return null,
                }
            }
        }

        fn parse(state: *@This()) ?i64 {
            if (state.index >= state.text.len) return null;
            switch (state.text[state.index]) {
                '0'...'9' => return state.parseInternal(),
                '-' => {
                    state.index += 1;
                    var x = state.parse() orelse return null;
                    return -x;
                },
                else => return null,
            }
        }
    };

    var expr = std.ArrayList(Lit).init(self.allocator);
    defer expr.deinit();

    while (index < text.len) {
        if (text[index] == ' ' or text[index] == '\t' or text[index] == '\n') {
            index += 1;
            continue;
        }

        // parse comment
        if (text[index] == 'c' or text[index] == 'p') {
            while (index < text.len and text[index] != '\n')
                index += 1;
            continue;
        }
        // parse clause
        while (index < text.len) {
            if (text[index] == ' ' or text[index] == '\n' or text[index] == '\t') {
                index += 1;
                continue;
            }

            var p = IntParser{ .index = index, .text = text };
            var lit = p.parse() orelse unreachable;
            index = p.index;

            if (lit == 0) break;

            var variable = if (lit > 0) lit else -lit;

            while (self.variables.len <= variable) {
                _ = try self.addVariable();
            }

            try expr.append(Lit.init(@intCast(variable), lit > 0));
        }

        try self.addClause(&expr);
        expr.clearRetainingCapacity();
        if (self.is_unsat) |_|
            return;
    }

    return;
}

test "random clause manager test" {
    //var rnd = std.rand.DefaultPrng.init(0);

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
        //if (entry.kind == .File) {
        var solver = try Solver(void).init(allocator);
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

        try solver.parse(buffer);

        var skip_file = false;
        for ("sudoku.cnf", 0..) |c, i| {
            if (i >= entry.name.len or entry.name[i] != c) {
                skip_file = true;
                break;
            }
        }

        //if (!skip_file) continue;

        const assumptions: [0]Lit = undefined;
        var b = try solver.cdcl(assumptions[0..]);
        if (b) try std.testing.expect(solver.checkModel());
        std.debug.print("{}\n", .{b});

        if (!b) {
            std.debug.print("final analyze length: {}\n", .{solver.final_conflict.items.len});
            const result = try std.ChildProcess.exec(.{
                .allocator = std.heap.page_allocator,
                .argv = &[_][]const u8{
                    "z3",
                    file_path,
                },
            });
            std.debug.print("{s}\n", .{result.stdout});
        }
        //}
    }
}
