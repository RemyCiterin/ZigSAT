
class BoolVar:
    ident = 3
    cnf = [[1], [-2]]

    def __init__(self, ident=None):
        if ident is None:
            self.ident = BoolVar.ident
            BoolVar.ident += 1
        else:
            self.ident = ident

    def getFalse():
        return BoolVar(2)

    def getTrue():
        return BoolVar(1)

    def isTrue(self):
        return self.ident == 1

    def isFalse(self):
        return self.ident == 2

    def fromBool(b):
        if b:
            return BoolVar.getTrue()
        return BoolVar.getFalse()

    def isBool(self):
        return self.ident <= 2

    def add_cnf(cnf: list[list[int]]):
        for clause in cnf:
            BoolVar.cnf.append(clause)

    def __and__(self, other):
        if self.isFalse() or other.isFalse():
            return BoolVar.getFalse()

        if self.isBool() and other.isBool():
            return BoolVar.fromBool(
                    self.isTrue() and other.isTrue())

        out = BoolVar()

        BoolVar.add_cnf([
            [self.ident, -out.ident],
            [other.ident, -out.ident],
            [out.ident, -self.ident, -other.ident]
            ])

        return out


    def __or__(self, other):

        if self.isTrue() or other.isTrue():
            return BoolVar.getTrue()

        if self.isBool() and other.isBool():
            return BoolVar.fromBool(self.isTrue() or other.isTrue())

        out = BoolVar()

        BoolVar.add_cnf([
            [-self.ident, out.ident],
            [-other.ident, out.ident],
            [-out.ident, self.ident, other.ident]
        ])

        return out


    def __invert__(self):
        if self.isBool():
            return BoolVar.fromBool(
                not self.isTrue())
        out = BoolVar()

        BoolVar.add_cnf([
            [self.ident, out.ident],
            [-out.ident, -self.ident]
        ])

        return out

    def __xor__(self, other):
        if self.isBool() and other.isBool():
            return BoolVar.fromBool(
                    self.isTrue() ^ other.isTrue())
        out = BoolVar()

        BoolVar.add_cnf([
            [self.ident, -other.ident, out.ident],
            [-self.ident, other.ident, out.ident],
            [self.ident, other.ident, -out.ident],
            [-self.ident, -other.ident, -out.ident]

        ])

        return out

    def __eq__(self, other):
        if self.isBool() and other.isBool():
            return BoolVar.fromBool(
                    self.isTrue() == other.isTrue())
        out = BoolVar()

        BoolVar.add_cnf([
            [-self.ident, -other.ident, out.ident],
            [self.ident, other.ident, out.ident],
            [self.ident, -other.ident, -out.ident],
            [-self.ident, other.ident, -out.ident]
        ])

        return out

    def ite(self, t, e):
        return (~self | t) & (self | e)

    def print_cnf(self):
        print("p cnf {} {}".format(BoolVar.ident, len(BoolVar.cnf)+1))
        print("{} 0".format(self.ident))
        for clause in BoolVar.cnf:
            for l in clause:
                print(end = "{} ".format(l))
            print("0")

    def __str__(self):
        s = "p cnf {} {}\n".format(BoolVar.ident, len(BoolVar.cnf)+1)
        s += "{} 0\n".format(self.ident)
        for clause in BoolVar.cnf:
            for l in clause:
                s += "{} ".format(l)
            s += "0\n"
        return s

    def clear():
        BoolVar.ident = 3
        BoolVar.cnf = [[1], [-2]]

F = BoolVar.getFalse()
T = BoolVar.getTrue()

class UBV:
    # data[i] is the bit number i of the bitvector
    def __init__(self, data: list[BoolVar]):
        self.data = data

    def var(l):
        return UBV([BoolVar() for _ in range(l)])

    def addWith(self, other, c):
        data = []

        for (x, y) in zip(self.data, other.data):
            data.append(x ^ y ^ c)
            c = (x & y) | (c & (x ^ y))

        return UBV(data), c

    def __getitem__(self, other):
        if isinstance(other, int):
            return self.data[other]

    def __iter__(self):
        for x in self.data:
            yield x

    def lshift(self, other, s):
        if s < 0: return self

        x = self.lshift(other, s-1)
        return UBV([other[s].ite(a, b) for a, b in zip(x << (2 ** s), x)])

    def __lshift__(self, x):
        if isinstance(x, int):
            data = []

            for _ in range(min(x, len(self.data))):
                data.append(BoolVar.getFalse())

            for y in self.data:
                if len(data) >= len(self.data):
                    break

                data.append(y)

            return UBV(data)

        assert(len(self.data) == 2 ** len(x.data))
        return self.lshift(x, len(x.data)-1)

    def __rshift__(self, x:int):
        s = UBV(list(reversed(self.data)))
        return UBV(list(reversed((s << x).data)))

    def __len__(self):
        return len(self.data)

    def __mul__(self, other):
        assert(len(self) == len(other))

        def mul(s):
            if s < 0: return UBV.fromInt(0, len(self))
            return mul(s-1) + UBV([
                other[s].ite(x, BoolVar.getFalse()) for x in self << s])

        return mul(len(self)-1)

    def __add__(self, other):
        return self.addWith(other, BoolVar.getFalse())[0]

    def __and__(self, other):
        return UBV([x & y for x, y in zip(self.data, other.data)])

    def __or__(self, other):
        return UBV([x | y for x, y in zip(self.data, other.data)])

    def __xor__(self, other):
        return UBV([x ^ y for x, y in zip(self.data, other.data)])

    def __eq__(self, other):
        eq = BoolVar.getTrue()

        for x, y in zip(self.data, other.data):
            eq = eq & (x == y)

        return eq

    def isZero(self):
        b = BoolVar.getTrue()
        for x in self.data: b = b & ~x
        return b

    def __le__(self, other):
        if len(self.data) == 0:
            return BoolVar.getTrue()

        lt = other.data[-1] & ~self.data[-1]
        eq = other.data[-1] == self.data[-1]

        out = lt | ((UBV(self.data[:-1]) <= UBV(other.data[:-1])) & eq)
        return out

    def __lt__(self, other):
        if len(self.data) == 0:
            return BoolVar.getFalse()
        lt = other.data[-1] & ~self.data[-1]
        eq = other.data[-1] == self.data[-1]

        out = lt | ((UBV(self.data[:-1]) < UBV(other.data[:-1])) & eq)
        return out

    def toInt(self):
        val = 0

        for i in range(len(self.data)):
            assert(self.data[i].isBool())
            val += (1 if self.data[i].isTrue() else 0) * 2 ** i

        return val

    def fromInt(val, bits):
        data = []
        in_val = val

        assert(val >= 0)
        assert(val < 2 ** bits)
        for _ in range(bits):
            data.append(BoolVar.fromBool(val % 2 == 1))
            val = val // 2
        assert(UBV(data).toInt() == in_val)

        return UBV(data)


class Grid:
    def __init__(self, size):
        self.values = {}
        self.size = size

    def get_row(self, row: int):
        return [(row, j) for j in range(self.size ** 2)]

    def get_col(self, col: int):
        return [(i, col) for i in range(self.size ** 2)]

    def get_square(self, i, j):
        return [(i*self.size+k, j*self.size+l)
                for k in range(self.size) for l in range(self.size)]

    def iter_row(self):
        return (self.get_row(row) for row in range(self.size ** 2))

    def iter_col(self):
        return (self.get_col(col) for col in range(self.size ** 2))

    def iter_square(self):
        return (self.square(i, j)
            for i in range(self.size) for j in range(self.size))

    def pairs(self, i, j):
        for _, l in self.get_row(i):
            if j != l: yield (i, l)

        for k, _ in self.get_col(j):
            if i != k: yield (k, j)

        for k, l in self.get_square(i // self.size, j // self.size):
            if (i, j) != (k, l): yield (k, l)

    def __iter__(self):
        for i in range(self.size ** 2):
            for j in range(self.size ** 2):
                for pair in self.pairs(i, j):
                    yield (i, j), pair

    def test_index(self, i, j):
        for pair in self.pairs(i, j):
            if (i, j) in self.values and pair in self.values:
                if self.values[i, j] == self.values[pair]:
                    return False
        return True

    def print(self):
        for j in range(self.size ** 2):
            if j % self.size == 0:
                for _ in range(1+ self.size * (self.size+1)):
                    print(end="-")
                print()
            for i in range(self.size ** 2):
                if i % self.size == 0: print(end="|")
                if (i, j) in self.values:
                    print(end=str(self.values[i, j]))
                else:
                    print(end=" ")
            print("|")
        for _ in range(1+ self.size * (self.size+1)):
            print(end="-")
        print()

    def test(self):
        for x, y in self:
            if x in self.values and y in self.values:
                if self.values[x] == self.values[y]:
                    return False
        return True

class Sudoku:
    def __init__(self, grid):
        self.size = grid.size

        self.bits = 0
        while self.size * self.size >= 2 ** self.bits: self.bits += 1

        self.constraint = BoolVar.getTrue()
        self.data = [
            [UBV.fromInt(grid.values[i, j], self.bits)
             if (i, j) in grid.values else UBV.var(self.bits)
             for i in range(self.size * self.size)]
            for j in range(self.size * self.size)]

        for i in range(self.size ** 2):
            for j in range(self.size ** 2):
                self.addConstraint(
                    self.data[i][j] <= UBV.fromInt(self.size ** 2, self.bits))

                self.addConstraint(
                    UBV.fromInt(1, self.bits) <= self.data[i][j])

        cache = {}
        for x, y in grid:
            if (x, y) in cache:
                continue

            cache[x, y] = None
            cache[y, x] = None
            self.addDiff(x[0], x[1], y[0], y[1])

    def addConstraint(self, constraint):
        self.constraint = self.constraint & constraint

    def addDiff(self, i, j, k, l):
        self.addConstraint(
            ~(self.data[i][j] == self.data[k][l]))

# return a boolean variable `b` such that `b ==> grid is sat`
def add_sudoku(grid):
    constraint = BoolVar()
    data = {
            (i, j): grid.values[i, j] if (i, j) in grid.values else
            [BoolVar() for _ in range(grid.size ** 2)]
        for j in range(grid.size ** 2)
        for i in range(grid.size ** 2)}

    for i in range(grid.size ** 2):
        for j in range(grid.size ** 2):
            if isinstance(data[i, j], int):
                continue

    cache = {}
    cache_pair = {}
    for x, y in grid:
        if not x in cache and not isinstance(data[x], int):
            cache[x] = None

            for i in range(grid.size ** 2):
                for j in range(i+1, grid.size * 2):
                    BoolVar.add_cnf([
                        [-constraint.ident, -data[x][i].ident, -data[x][j].ident]
                    ])

            BoolVar.add_cnf([
                [-constraint.ident] +
                [data[x][i].ident for i in range(grid.size ** 2)]
            ])

        if (x, y) in cache_pair:
            continue

        cache_pair[x, y] = None
        cache_pair[y, x] = None

        if isinstance(data[x], int):
            if isinstance(data[y], int):
                continue

            BoolVar.add_cnf([[-constraint.ident, -data[y][data[x]-1].ident]])
            continue

        if isinstance(data[y], int):
            BoolVar.add_cnf([[-constraint.ident, -data[x][data[y]-1].ident]])
            continue

        for i in range(grid.size ** 2):
            BoolVar.add_cnf([
                [-constraint.ident, -data[x][i].ident, -data[y][i].ident],
            ])

    return constraint


import random
import os

def gen_grid(size, num):
    grid = Grid(size)

    while num > 0:
        i = random.randint(0, (size ** 2) - 1)
        j = random.randint(0, (size ** 2) - 1)
        v = random.randint(1, size ** 2)

        if (i, j) in grid.values:
            continue

        is_valid = True
        for pair in grid.pairs(i, j):
            if pair in grid.values and grid.values[pair] == v:
                is_valid = False

        if not is_valid: continue

        grid.values[i, j] = v
        num -= 1

    return grid

'''
for _ in range(10):
    grid = gen_grid(3, 24)

    grid.print()
    #s = Sudoku(grid)
    #constraints = constraints | s.constraint

    f = open("./test.cnf", "w")
    f.write(str(add_sudoku(grid)))
    f.close()

    os.system("../zig-out/bin/ZigSAT ./test.cnf")

    BoolVar.clear()

    f = open("./test.cnf", "w")
    f.write(str(Sudoku(grid).constraint))
    f.close()

    os.system("../zig-out/bin/ZigSAT ./test.cnf")
    BoolVar.clear()

    print("\n-----------------------------------\n")
'''

def rand(N):
    while True:
        n = random.randint(3, N)

        test=True
        for i in range(2, min(1000, n)):
            if n % i == 0:
                test = False
                break

        if test:
            return n

def facto(N, bits):
    n = 1+int(N ** 0.5)
    n = UBV.fromInt(n, bits)
    N = UBV.fromInt(N, bits)

    x = UBV.var(bits)
    y = UBV.var(bits)

    return (x * y == N) & (y < N) & (x < N)


import subprocess
import matplotlib.pyplot as plt

import numpy as np
import threading
import time

def benchmark(prog):
    times = []
    queue = []

    threads = 6
    busy = [False for _ in range(threads)]

    def run(index):
        p = subprocess.Popen(prog) #[prog,
            #'./test.cnf', '-no-pre',  '-phase-saving=2', '-ccmin-mode=1'])
        t = time.time()
        try:
            p.wait(10)
        except subprocess.TimeoutExpired:
            p.kill()
        times.append(time.time() - t)
        busy[index] = False
        print(time.time()-t)

    for _ in range(30):
        #grid = gen_grid(5, 250)
        #constraint = add_sudoku(grid)

        #grid = gen_grid(3, 25)
        #constraint = Sudoku(grid).constraint

        N = rand(2 ** 20)
        print(N)
        constraint = facto(N, 42)

        #grid.print()
        time.sleep(0.1)
        f = open("./test.cnf", "w")
        f.write(str(constraint))
        f.close()


        if len(queue) < threads:
            busy[len(queue)] = True
            queue.append(threading.Thread(target=run, args=(len(queue),)))
            queue[-1].start()

        else:
            stop = False
            while not stop:
                for index in range(threads):
                    if not busy[index]:
                        busy[index] = True
                        queue[index].join()
                        queue[index] = \
                            threading.Thread(target=run, args=(index,))
                        queue[index].start()
                        stop = True
                        break

        BoolVar.clear()

    for p in queue:
        p.join()

    return times



plt.plot(np.sort(benchmark(
    ['kissat', 'test.cnf'])), label='kissat')
plt.plot(np.sort(benchmark(
    ['../zig-out/bin/ZigSAT', 'test.cnf'])), label="ZigSAT")
plt.plot(np.sort(benchmark(
    ['../mathsat', '-input=dimacs', 'test.cnf'])), label="mathsat")
plt.plot(np.sort(benchmark(
    ['../minisat', 'test.cnf', '-ccmin-mode=1', '-phase-saving=2', '-no-luby'])), label="minisat")
#plt.plot(np.sort(benchmark(
#    ['../glucose_static', 'test.cnf', '-ccmin-mode=1', '-phase-saving=2'])), label="glucose2")
plt.plot(np.sort(benchmark(
    ['glucose', 'test.cnf', '-no-pre', '-ccmin-mode=1', '-phase-saving=2'])), label="glucose4")
plt.yscale("log")
plt.legend()
plt.show()

