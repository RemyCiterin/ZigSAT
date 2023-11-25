with (import <nixpkgs> {});
mkShell {
  buildInputs = [
    #linuxKernel.packages.linux_6_3.perf
    python310Packages.matplotlib
    python310Packages.tkinter
    python310Packages.numpy
    tcl
    tk
    python310
    minisat
    glucose
    cadical
    kissat
  ];

  shellHook = ''
      export TK_LIBRARY="${pkgs.tk}/lib/${pkgs.tk.libPrefix}"
  '';

}
