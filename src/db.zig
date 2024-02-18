const std = @import("std");

// a type of database, for the moment it doesn't use MultiArrayList nut just ArrayList
pub fn DB(comptime T: type) type {
    return struct {
        const Self = @This();
        pub const Id = struct {
            index: u32,
            generation: u16,

            pub fn equal(self: @This(), other: @This()) bool {
                return self.index == other.index and self.generation == other.generation;
            }
        };

        pub const Iterator = struct {
            view: *Self,
            index: u32,

            pub fn next(self: *@This()) ?Id {
                while (true) {
                    if (self.index >= self.view.elems.items.len) return null;

                    if (!self.view.allocated.items[self.index]) {
                        self.index += 1;
                        continue;
                    }

                    var gen = self.view.generation.items[self.index];
                    var id = Id{ .index = self.index, .generation = gen };
                    self.index += 1;
                    return id;
                }
            }
        };

        elems: std.ArrayList(T),
        generation: std.ArrayList(u16),

        allocated: std.ArrayList(bool),

        /// free list is an array of size `elems.items.len`, only the index `0..free_list_idx` are important:
        /// this allow to doesn't allocate memory on call to free!
        free_list: std.ArrayList(u32),

        free_list_idx: usize,

        pub fn init(allocator: std.mem.Allocator) Self {
            return Self{
                .elems = std.ArrayList(T).init(allocator),
                .generation = std.ArrayList(u16).init(allocator),
                .allocated = std.ArrayList(bool).init(allocator),
                .free_list = std.ArrayList(u32).init(allocator),
                .free_list_idx = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            self.generation.deinit();
            self.free_list.deinit();
            self.allocated.deinit();
            self.elems.deinit();
        }

        pub fn isFree(self: Self, id: Id) bool {
            return id.generation != self.generation.items[id.index];
        }

        pub fn free(self: *Self, id: Id) void {
            if (self.isFree(id)) @panic("use of an invalid Id");
            if (!self.allocated.items[id.index]) @panic("already free");
            self.free_list.items[self.free_list_idx] = id.index;
            self.allocated.items[id.index] = false;
            self.generation.items[id.index] +%= 1;
            self.free_list_idx += 1;
        }

        pub fn len(self: Self) usize {
            return self.elems.items.len - self.free_list_idx;
        }

        pub fn iter(self: *Self) Iterator {
            return .{ .view = self, .index = 0 };
        }

        pub fn alloc(self: *Self, t: T) !Id {
            if (self.free_list_idx == 0) {
                var id = Id{
                    .index = @intCast(self.elems.items.len),
                    .generation = 0,
                };

                try self.free_list.append(undefined);
                try self.allocated.append(true);
                try self.generation.append(0);
                try self.elems.append(t);
                return id;
            }

            self.free_list_idx -= 1;
            var index = self.free_list.items[self.free_list_idx];
            var generation = self.generation.items[index];

            if (self.allocated.items[index]) @panic("already allocated");
            var id = Id{ .index = index, .generation = generation };

            self.elems.items[index] = t;
            self.allocated.items[index] = true;

            return id;
        }

        // a tmp borrow of a object of the database
        pub fn borrow(self: Self, id: Id) *T {
            if (self.isFree(id)) @panic("use of an invalid Id");
            return &self.elems.items[id.index];
        }
    };
}
