with (import <nixpkgs> {});
mkShell {
  buildInputs = [
    linuxKernel.packages.linux_6_3.perf
    minisat
  ];

}
