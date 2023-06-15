

profile: build
	time perf record --call-graph=dwarf -- zig-out/bin/ZigSAT test.cnf
	perf report
	rm -rf perf.data
	rm -rf perf.data.old

minisat0:
	./minisat test.cnf -phase-saving=0 -ccmin-mode=0 -no-luby

minisat2:
	./minisat test.cnf -phase-saving=0 -ccmin-mode=2 -no-luby

build:
	zig build -Drelease-fast=true

run:
	time zig-out/bin/ZigSAT test.cnf

test:
	zig test src/solver.zig
