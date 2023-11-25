//! this file define some parser combinator to parse dimacs file
const std = @import("std");
const Lit = @import("lit.zig").Lit;
const lbool = @import("lit.zig").lbool;

/// a type of reader with the possibility to backtrack
const Input = struct {
    buffer: []const u8,
    index: usize = 0,
    line: usize = 1,
    col: usize = 1,

    const Self = @This();

    pub fn read(self: Self, len: usize) []const u8 {
        var max_index = @min(self.index + len, self.buffer.len);
        return self.buffer[self.index..max_index];
    }

    pub fn next(self: Self) Result(u8) {
        if (self.index >= self.buffer.len)
            return null;

        var char = self.buffer[self.index];
        var out = Self{ .buffer = self.buffer, .index = self.index };

        if (char == '\n') {
            out.line = self.line + 1;
            out.col = 0;
        } else {
            out.line = self.line;
            out.col = self.col + 1;
        }

        return .{ .next_input = out, .result = self.buffer[self.index] };
    }
};

pub fn Result(comptime T: type) type {
    return ?struct {
        next_input: Input,
        result: T,
    };
}

pub fn Parser(comptime Context: type, comptime Err: type, comptime T: type) type {
    return struct {
        context: Context,
        _parse: *const fn (Context, Input) Err!Result(T),

        pub const Error = Err;
        const Self = @This();

        pub fn parse(self: Self, input: Input) Err!Result(T) {
            return self._parse(self.context, input);
        }
    };
}

pub const CharParser = struct {
    const Self = @This();
    char: u8,

    pub fn parse(self: Self, input: Input) error{}!Result(u8) {
        if (input.next()) |res| {
            if (res.result == self.char)
                return res;
        }
        return null;
    }

    pub fn init(char: u8) Self {
        return Self{ .char = char };
    }

    const ParserType = Parser(Self, error{}, u8);

    pub fn parser(self: Self) ParserType {
        return ParserType{ .context = self, ._parse = parse };
    }
};

fn mulWithOverflow(comptime T: type, a: T, b: T, res: *T) bool {
    var out = @mulWithOverflow(a, b);
    res.* = out[0];
    return out[1];
}

fn addWithOverflow(comptime T: type, a: T, b: T, res: *T) bool {
    var out = @addWithOverflow(a, b);
    res.* = out[0];
    return out[1];
}

pub fn IntParser(comptime T: type, comptime base: T) type {
    if (base <= 1) @compileError("base should be greater than one");

    return struct {
        const bits = switch (@typeInfo(T)) {
            .Int => |info| info.bits,
            else => @compileError("only runtime integer accepted"),
        };

        const signedness = switch (@typeInfo(T)) {
            .Int => |info| info.signedness,
            else => @compileError("only runtime integer accepted"),
        };

        const Self = @This();
        begin: usize,
        end: usize,

        /// assume that buffer[self.begin..self.end] is an
        /// integer and parse it, return null if this integer is too large
        pub fn parseInt(self: Self, buffer: []const u8) ?T {
            var idx: usize = self.end - 1;
            var power: T = 1;
            var out: T = 0;

            while (idx >= self.begin) : (idx -= 1) {
                var x: T = undefined;

                if (mulWithOverflow(T, buffer[idx], power, &x))
                    return null;

                if (addWithOverflow(T, x, out, &out))
                    return null;

                if (idx != self.begin) {
                    if (mulWithOverflow(T, power, base, &power))
                        return null;
                }
            }

            return out;
        }

        pub fn parseInternal(self: *Self, input: Input) error{}!Result(T) {
            _ = self;
            _ = input;
            @panic("");
        }
    };
}

test "parser test" {
    const input = Input{ .buffer = "b" };

    var parser = CharParser.init('b').parser();

    var res = try parser.parse(input);
    try std.testing.expect(res.?.result == 'b');
}
