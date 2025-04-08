{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    python3
    python3Packages.z3
    python3Packages.pytest
    python3Packages.pip
    python3Packages.setuptools
    python3Packages.wheel
  ];
  
  shellHook = ''
    # Set up local development environment
    export PYTHONPATH="$PWD/src:$PYTHONPATH"
    export PATH="$PWD:$PATH"
    
    # Make dev_cli.py executable
    chmod +x $PWD/dev_cli.py
    
    echo "ModelChecker development environment activated"
    echo "Run './dev_cli.py example.py' to use local source code"
  '';
}