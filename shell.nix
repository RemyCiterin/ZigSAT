with (import <nixpkgs> {});
mkShell {
  buildInputs = [
    linuxKernel.packages.linux_6_3.perf
    python311Packages.matplotlib
    python311Packages.tkinter
    python311Packages.numpy
    tcl
    tk
    python311
    minisat
    glucose
    cadical
    kissat
  ];

  shellHook = ''
      export TK_LIBRARY="${pkgs.tk}/lib/${pkgs.tk.libPrefix}"
  '';

}
