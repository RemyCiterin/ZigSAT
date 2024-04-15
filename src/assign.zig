// This file define a type of assignation stack for the SAT solver

const std = @import("std");
const Lit = @import("lit.zig").Lit;
const lbool = @import("lit.zig").lbool;
const Variable = @import("lit.zig").Variable;
const meta = std.meta;

const Allocator = std.mem.Allocator;

pub fn AssignStack(comptime Reason: type, comptime Proof: type) type {
    return struct {
        const VarData = struct {
            level: ?u32 = null,
            proof: ?Proof = null,
            reason: ?Reason = null,
            position: ?usize = null,
            value: lbool = lbool.lundef,
        };

        level: u32 = 0,

        allocator: Allocator,

        stack: std.ArrayListUnmanaged(Lit) = .{},

        var_data: std.MultiArrayList(VarData) = .{},

        const Self = @This();

        pub fn init(allocator: Allocator) Self {
            return .{ .allocator = allocator };
        }

        pub fn deinit(self: *Self) void {
            for (self.var_data.items(.proof)) |proof| {
                if (proof) |p| p.deinit();
            }

            self.stack.deinit(self.allocator);
            self.var_data.deinit(self.allocator);
        }

        pub fn get(
            self: Self,
            v: Variable,
            comptime arg: meta.FieldEnum(VarData),
        ) meta.fieldInfo(VarData, arg).type {
            // if the variable doesn't exist, return it's default value
            if (v >= self.var_data.len) {
                return @field(VarData{}, @tagName(arg));
            }

            return self.var_data.items(arg)[v];
        }

        /// return a view to it's assignation stack
        pub fn view(self: Self) []const Lit {
            return self.stack.items;
        }

        /// return the value of assignation of a literal
        pub fn value(self: Self, l: Lit) lbool {
            var b = self.get(l.variable(), .value);
            return if (l.sign()) b else b.not();
        }

        /// update the reason of assignation of a variable
        pub fn updateReason(self: *Self, v: Variable, reason: Reason) void {
            std.debug.assert(self.get(v, .reason) != null);
            self.var_data.items(.reason)[v] = reason;
        }

        /// add a variable into the database
        pub fn addVariable(self: *Self) Allocator.Error!Variable {
            var v = self.var_data.len;
            try self.var_data.append(self.allocator, .{});
            return @truncate(v);
        }

        pub fn len(self: Self) usize {
            return self.var_data.len;
        }

        /// return the last assignation
        pub fn lastAssign(self: Self) ?Lit {
            if (self.stack.items.len > 0)
                return self.stack.items[self.stack.items.len - 1];
            return null;
        }

        /// add one to the current level
        pub fn push(self: *Self) void {
            self.level += 1;
        }

        fn iff(x: bool, y: bool) bool {
            return if (x) y else !y;
        }

        /// add an assignation
        pub fn assign(self: *Self, lit: Lit, reason: ?Reason, proof: ?Proof) Allocator.Error!void {
            while (lit.variable() >= self.var_data.len) _ = try self.addVariable();

            var last_level =
                if (self.lastAssign()) |l| self.get(l.variable(), .level).? else 0;

            std.debug.assert(iff(proof == null and reason == null, self.level > last_level));
            std.debug.assert(iff(proof == null, self.level > 0));
            std.debug.assert(self.value(lit) == lbool.lundef);

            self.var_data.set(lit.variable(), .{
                .position = if (self.level > 0) self.stack.items.len else null,
                .value = lbool.init(lit.sign()),
                .level = self.level,
                .reason = reason,
                .proof = proof,
            });

            if (self.level > 0) try self.stack.append(self.allocator, lit);
        }

        /// force an assignation at level zero
        pub fn assignZero(self: *Self, lit: Lit, proof: Proof) Allocator.Error!void {
            while (lit.variable() >= self.var_data.len) _ = try self.addVariable();

            self.var_data.set(lit.variable(), .{
                .value = lbool.init(lit.sign()),
                .position = null,
                .reason = null,
                .proof = proof,
                .level = 0,
            });
        }

        /// pop the previous assignation
        pub fn pop(self: *Self) void {
            var v = self.stack.pop().variable();

            // we can't pop at level 0
            std.debug.assert(self.level != 0);

            if (self.get(v, .reason) == null) self.level -= 1;
            self.var_data.set(v, .{});
        }
    };
}
