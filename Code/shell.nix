{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = with pkgs.python3Packages; [
    pip
    setuptools
    wheel
    virtualenv
    z3-solver
  ];

  # Set PYTHONPATH to include the src directory
  shellHook = ''
    export PYTHONPATH=${toString ./src}:$PYTHONPATH
  '';
}
