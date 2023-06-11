

profile:
	zig build -Drelease-fast=true
	time perf record --call-graph=dwarf -- zig-out/bin/ZigSAT
	perf report
	rm -rf perf.data
	rm -rf perf.data.old

run-minisat:
	minisat test.cnf -no-pre -ccmin-mode=0 -no-elim

