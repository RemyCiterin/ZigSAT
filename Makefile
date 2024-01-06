

profile: build
	time perf record --call-graph=dwarf -- zig-out/bin/ZigSat ./test.cnf
	perf report
	rm -rf perf.data
	rm -rf perf.data.old

minisat0:
	./minisat test.cnf -phase-saving=0 -ccmin-mode=0 -no-luby

minisat2:
	./minisat test.cnf -phase-saving=0 -ccmin-mode=2 -no-luby

glucose:
	./glucose_static test.cnf -no-pre -ccmin-mode=2

build:
	zig build -Doptimize=ReleaseFast

run:
	time zig-out/bin/ZigSat test.cnf

test:
	zig test src/solver.zig
