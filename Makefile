TEST = ./test-generator/BV2/sudoku.cnf # ./test-generator/test.cnf

# measure the performances of each function calls
profile: build
	time perf record --call-graph=dwarf -- zig-out/bin/ZigSat $(TEST)
	perf report
	rm -rf perf.data
	rm -rf perf.data.old

# measure the number of cache misses
stats:
	perf stat -B -e cache-references,cache-misses,cycles,instructions,branches,faults,migrations \
		./zig-out/bin/ZigSat $(TEST)

stats_baseline:
	perf stat -B -e cache-references,cache-misses,cycles,instructions,branches,faults,migrations \
		./test-generator/zigsat_baseline $(TEST)

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
