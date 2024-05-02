with (import <nixpkgs> {});
mkShell {
  buildInputs = [
    linuxKernel.packages.linux_6_6.perf
    minisat
    glucose
    cadical
    kissat
  ];

  shellHook = ''
      export TK_LIBRARY="${pkgs.tk}/lib/${pkgs.tk.libPrefix}"
  '';

}
