const std = @import("std");

pub const lbool = enum(u2) {
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

    pub fn not(self: lbool) lbool {
        return switch (self) {
            .ltrue => lbool.lfalse,
            .lfalse => lbool.ltrue,
            else => lbool.lundef,
        };
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

    pub fn toInt(self: lbool) u2 {
        return @intFromEnum(self);
    }

    pub fn fromInt(x: u2) lbool {
        return @enumFromInt(x);
    }
};

test "test lbool" {
    try std.testing.expect(lbool.ltrue.land(.ltrue) == .ltrue);
    try std.testing.expect(lbool.ltrue.land(.lfalse) == .lfalse);
    try std.testing.expect(lbool.ltrue.land(.lundef) == .lundef);
    try std.testing.expect(lbool.lfalse.land(.lfalse) == .lfalse);
    try std.testing.expect(lbool.lfalse.land(.lundef) == .lfalse);
}

pub const Variable = u31;

pub fn variableToUsize(v: Variable) usize {
    return @intCast(v);
}

pub const Lit = packed struct(u32) {
    val: Variable,
    tag: bool,

    const Self = @This();

    pub fn init(v: Variable, value: bool) Self {
        return Self{ .val = v, .tag = value };
    }

    pub fn not(self: Self) Self {
        return Self{ .val = self.val, .tag = !self.tag };
    }

    pub fn variable(self: Self) u31 {
        return self.val;
    }

    pub fn sign(self: Self) bool {
        return self.tag;
    }

    pub fn equals(self: Self, other: Self) bool {
        return self.variable() == other.variable() and self.sign() == other.sign();
    }

    pub fn toInt(self: Self) u32 {
        return @bitCast(self);
    }

    pub fn fromInt(x: u32) Self {
        return @bitCast(x);
    }
};

pub fn generateClause(expr: *std.ArrayList(Lit)) !bool {
    const sortFn = struct {
        fn lessThan(ctx: void, l1: Lit, l2: Lit) bool {
            _ = ctx;

            if (l1.variable() != l2.variable())
                return l1.variable() < l2.variable();

            return l1.sign() and !l2.sign();
        }
    };

    std.mem.sort(Lit, expr.items, {}, sortFn.lessThan);

    var l: ?Lit = null;
    var i: usize = 0;

    while (i < expr.items.len) {
        var lit = expr.items[i];
        if (l != null and lit.equals(l.?.not()))
            return true;

        if (l == null or !lit.equals(l.?)) {
            l = lit;
            i += 1;
        } else {
            _ = expr.swapRemove(i);
        }
    }

    return false;
}
