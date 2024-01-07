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
        return @intFromEnum(self);
    }

    pub fn fromInt(x: u8) lbool {
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

const LitError = error{InvalidIntegerRepresentation};

pub const LitTag = enum(u1) { pos, neg };

pub const Variable = u31;

pub fn variableToUsize(v: Variable) usize {
    return @intCast(v);
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
        return switch (self) {
            .pos => |v| Self{ .neg = v },
            .neg => |v| Self{ .pos = v },
        };
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

        return (@as(u32, x) << 1) | @intFromEnum(@as(LitTag, self));
    }

    pub fn fromInt(x: u32) LitError!Self {
        var tag: LitTag = @enumFromInt(@as(u1, @truncate(x)));
        switch (tag) {
            .pos => return Lit{ .pos = @as(u31, @intCast(x >> 1)) },
            .neg => return Lit{ .neg = @as(u31, @intCast(x >> 1)) },
        }
    }
};

pub const lit_undef: Lit = Lit.lit_undef;
pub const lit_error: Lit = Lit.lit_error;

/// return true if the clause is trivialy unsat
//pub fn generateClause(new_expr: *std.ArrayList(Lit), expr: []Lit) !bool {
//    const sortFn = struct {
//        fn lessThan(ctx: void, l1: Lit, l2: Lit) bool {
//            _ = ctx;
//
//            if (l1.variable() != l2.variable())
//                return l1.variable() < l2.variable();
//
//            return l1.sign() and !l2.sign();
//        }
//    };
//
//    new_expr.clearRetainingCapacity();
//
//    std.mem.sort(Lit, expr, {}, sortFn.lessThan);
//
//    var l: ?Lit = null;
//    for (expr) |lit| {
//        if (l != null and lit.equals(l.?.not()))
//            return true;
//
//        if (l == null or !lit.equals(l.?)) {
//            try new_expr.append(lit);
//            l = lit;
//        }
//    }
//
//    return false;
//}

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
