const std = @import("std");
const Solver = @import("solver.zig").Solver;
const Lit = @import("lit.zig").Lit;

pub fn main() !void {
    //var rnd = std.rand.DefaultPrng.init(0);
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        _ = gpa.deinit();
    }

    var expr = std.ArrayList(Lit).init(allocator);
    defer expr.deinit();

    var solver = Solver.init(allocator);
    defer solver.deinit();

    const file_path =
        try std.fmt.allocPrint(allocator, "test.cnf", .{});
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

    var b = try solver.cdcl();
    if (b) try std.testing.expect(solver.checkModel());
    std.debug.print("{}\n", .{b});
}
