const std = @import("std");

pub const lbool = enum(u8) {
    lfalse,
    ltrue,
    lundef,

    pub fn init(x: bool) lbool {
        if (x) {
            return .ltrue;
        } else {
            return .lfalse;
        }
    }

    pub fn sign(self: lbool) bool {
        switch (self) {
            .ltrue => return true,
            .lfalse => return false,
            else => @panic("undef lbool"),
        }
    }

    pub fn land(x: lbool, y: lbool) lbool {
        if (x == .lfalse or y == .lfalse) {
            return .lfalse;
        }
        if (x == .ltrue and y == .ltrue) {
            return .ltrue;
        }
        return .lundef;
    }

    pub fn lor(x: lbool, y: lbool) lbool {
        if (x == .ltrue or y == .ltrue) {
            return .ltrue;
        }
        if (x == .lfalse and y == .lfalse) {
            return .lfalse;
        }
        return .lundef;
    }

    pub fn lxor(x: lbool, y: lbool) lbool {
        _ = x;
        _ = y;
        unreachable;
    }

    pub fn toInt(self: lbool) u8 {
        return @enumToInt(self);
    }

    pub fn fromInt(x: u8) lbool {
        return @intToEnum(lbool, x);
    }
};

test "test lbool" {
    try std.testing.expect(lbool.ltrue.land(.ltrue) == .ltrue);
    try std.testing.expect(lbool.ltrue.land(.lfalse) == .lfalse);
    try std.testing.expect(lbool.ltrue.land(.lundef) == .lundef);
    try std.testing.expect(lbool.lfalse.land(.lfalse) == .lfalse);
    try std.testing.expect(lbool.lfalse.land(.lundef) == .lfalse);
}

const LitError = error{InvalidIntegerRepresentation};

pub const LitTag = enum(u1) { pos, neg };

pub const Variable = u31;

pub fn variableToUsize(v: Variable) usize {
    return @intCast(usize, v);
}

pub const Lit = union(LitTag) {
    pos: u31,
    neg: u31,

    const Self = @This();

    pub fn init(v: u31, value: bool) Self {
        if (value) {
            return Self{ .pos = v };
        } else {
            return Self{ .neg = v };
        }
    }

    pub fn not(self: Self) Self {
        return Self.init(self.variable(), !self.sign());
    }

    pub fn variable(self: Self) u31 {
        switch (self) {
            .pos => |v| return v,
            .neg => |v| return v,
        }
    }

    pub fn sign(self: Self) bool {
        switch (self) {
            .neg => return false,
            .pos => return true,
        }
    }

    pub fn equals(self: Self, other: Self) bool {
        return self.variable() == other.variable() and self.sign() == other.sign();
    }

    pub fn toInt(self: Self) u32 {
        var x: u31 = undefined;

        switch (self) {
            .pos => |v| {
                x = v;
            },
            .neg => |v| {
                x = v;
            },
        }

        return (@intCast(u32, x) << 1) | @enumToInt(@as(LitTag, self));
    }

    pub fn fromInt(x: u32) LitError!Self {
        var tag = @intToEnum(LitTag, @truncate(u1, x));
        switch (tag) {
            .pos => return Lit{ .pos = @intCast(u31, x >> 1) },
            .neg => return Lit{ .neg = @intCast(u31, x >> 1) },
        }
    }
};

pub const lit_undef: Lit = Lit.lit_undef;
pub const lit_error: Lit = Lit.lit_error;

test "test lit" {
    var rnd = std.rand.DefaultPrng.init(0);

    var i: usize = 0;
    while (i < 1000) : (i += 1) {
        var x = rnd.random().int(u31);

        var p1 = Lit{ .pos = x };
        var n1 = Lit{ .neg = x };
        var p2 = try Lit.fromInt(p1.toInt());
        var n2 = try Lit.fromInt(n1.toInt());

        try std.testing.expect(p1.equals(p2));
        try std.testing.expect(n1.equals(n2));
    }
}
