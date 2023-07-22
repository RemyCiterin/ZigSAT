//! this file define some parser combinator to parse dimacs file
const std = @import("std");
const Lit = @import("lit.zig").Lit;
const lbool = @import("lit.zig").lbool;
const Variable = @import("lit.zig").Variable;

pub fn parseDIMACS(allocator: std.mem.Allocator, text: []u8, output: *std.ArrayList([]Lit)) !usize {
    var index: usize = 0;

    var max_variable: usize = 0;

    const IntParser = struct {
        index: usize,
        text: []u8,

        fn parseInternal(state: *@This(), x: i64) ?i64 {
            if (state.index >= state.text.len) return x;
            var char = state.text[state.index];

            switch (char) {
                '0'...'9' => {
                    var y = char - '0';
                    state.index += 1;
                    return state.parseInternal(x * 10 + y);
                },
                ' ', '\n', '\t' => return x,
                else => return null,
            }
        }

        fn parse(state: *@This()) ?i64 {
            if (state.index >= state.text.len) return null;
            switch (state.text[state.index]) {
                '0'...'9' => return state.parseInternal(0),
                '-' => {
                    state.index += 1;
                    var x = state.parse() orelse return null;
                    return -x;
                },
                else => return null,
            }
        }
    };

    var expr = std.ArrayList(Lit).init(allocator);
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

            var variable = @intCast(usize, if (lit > 0) lit else -lit);

            if (variable > max_variable)
                max_variable = variable;

            try expr.append(Lit.init(@intCast(Variable, variable), lit > 0));
        }

        var expr_copy = try allocator.alloc(Lit, expr.items.len);
        std.mem.copy(Lit, expr_copy, expr.items);
        expr.clearRetainingCapacity();
        try output.append(expr_copy);
    }

    return max_variable;
}
