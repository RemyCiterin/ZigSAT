const std = @import("std");

/// a function that take as input a type, raise an `@comptimeError(...)` if it doesn't satisfy a certain set
/// of declarations. As example
/// ```
/// pub const Point = struct {
///     pub const Data = i32;
///     x: Data, y: Data,
///     pub fn getx(self: @This()) Data {return self.x;}
///     pub fn gety(self: @This()) Data {return self.y;}
/// };
///
/// pub fn traitPoint(comptime T: type) {
///     return .{
///         .{ .name= "Data", .type= type, .doc= "`Data` represent a scalar type" }
///         .{ .name= "getx", .type= fn (T) T.Data },
///         .{ .name= "gety" },
///     };
/// };
///
/// comptime Trait(Point, traitPoint(Point)); // Success!!!
///
/// const ErrorTrait = .{.{ .name= "NotPresent", .doc= "a doc for `NotPresent`" }};
/// comptime Trait(Point, ErrorTrait); // Error!!!
/// ```
pub fn Trait(comptime T: type, comptime eqs: anytype) void {
    comptime {
        for (eqs) |eq| {
            var Eq = @TypeOf(eq);
            var msg0 = "`" ++ @typeName(T) ++ "` must have a declaration `" ++ eq.name ++ "`";

            var msg1 = if (@hasField(Eq, "type"))
                msg0 ++ " of type `" ++ @typeName(eq.type) ++ "`"
            else
                msg0;

            var msg = if (@hasField(Eq, "doc"))
                msg1 ++ "\ndoc:\n" ++ eq.doc ++ "\n"
            else
                msg1;

            if (!@hasDecl(T, eq.name))
                @compileError(msg);

            if (!@hasField(Eq, "type")) continue;

            if (!std.meta.eql(@TypeOf(@field(T, eq.name)), eq.type))
                @compileError(msg);
        }
    }
}
