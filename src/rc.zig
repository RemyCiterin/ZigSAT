const std = @import("std");

// reference counting
pub fn Rc(comptime T: type) type {
    return struct {
        ptr: *T,
        counter: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) !Self {
            const ptr = try allocator.create(T);
            return Self{ .allocator = allocator, .ptr = ptr, .counter = 1 };
        }

        pub fn borrow(self: *Self) *T {
            return self.ptr;
        }

        pub fn clone(self: *Self) *Self {
            self.counter += 1;
            return self;
        }

        pub fn deinit(self: *Self) void {
            if (self.counter == 1) {
                self.allocator.destroy(self.ptr);
            }
            self.counter -= 1;
        }
    };
}

test "reference counting test" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        _ = gpa.deinit();
    }

    var ref0 = try Rc(u32).init(allocator);
    defer ref0.deinit();

    ref0.borrow().* = 42;

    var ref1: *Rc(u32) = ref0.clone();
    ref1.borrow().* = 43;

    var ref2 = ref0.clone();
    try std.testing.expect(ref2.borrow().* == 43);

    ref1.deinit();
    ref2.deinit();
}
