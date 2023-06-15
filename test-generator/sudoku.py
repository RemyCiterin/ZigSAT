
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

    def print_cnf(self):
        print("p cnf {} {}".format(BoolVar.ident, len(BoolVar.cnf)+1))
        print("{} 0".format(self.ident))
        for clause in BoolVar.cnf:
            for l in clause:
                print(end = "{} ".format(l))
            print("0")

    def clear():
        BoolVar.ident = 0
        BoolVar.cnf = []

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

class Sudoku:
    def __init__(self, size):

        self.bits = 0
        while size * size >= 2 ** self.bits: self.bits += 1

        self.constraint = BoolVar.getTrue()
        self.data = [
            [UBV.var(self.bits) for _ in range(size * size)] for _ in range(size * size)]

        for i in range(size * size):
            for j in range(size * size):
                self.addConstraint(
                    self.data[i][j] <= UBV.fromInt(size * size, self.bits))
                self.addConstraint(
                    UBV.fromInt(1, self.bits) <= self.data[i][j])

                # check the line
                for k in range(size * size):
                    if k < j:
                        self.addConstraint(
                            ~(self.data[i][j] == self.data[i][k]))

                    if k < i:
                        self.addConstraint(
                            ~(self.data[i][j] == self.data[k][j]))

                for k in range(i // size, (i+1) // size):
                    for l in range(j // size, (j+1) // size):
                        if k != i or l != j:
                            self.addConstraint(
                                ~(self.data[i][j] == self.data[k + (i // size)][l + (j //size)]))



    def fixValue(self, i, j, v):
        self.addConstraint(self.data[i][j] == v)

    def addConstraint(self, constraint):
        self.constraint = self.constraint & constraint


sudoku = Sudoku(3)



sudoku.constraint.print_cnf()
