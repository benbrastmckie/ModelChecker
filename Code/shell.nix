{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    python3
    python3Packages.z3
    python3Packages.pytest
    python3Packages.jupyter
    python3Packages.notebook
    python3Packages.ipywidgets
    python3Packages.matplotlib
    python3Packages.networkx
    python3Packages.pip
    python3Packages.setuptools
    python3Packages.wheel
  ];
  
  shellHook = ''
    # Set up local development environment
    export PYTHONPATH="$PWD:$PWD/src:$PYTHONPATH"
    export PATH="$PWD:$PATH"
    
    # Make dev_cli.py executable
    chmod +x $PWD/dev_cli.py
    
    # Create symlink for notebook import
    mkdir -p $HOME/.local/lib/python3.*/site-packages/model_checker
    ln -sf $PWD/src/model_checker/* $HOME/.local/lib/python3.*/site-packages/model_checker/ 2>/dev/null
    
    echo "ModelChecker development environment activated"
    echo "Run './dev_cli.py example.py' to use local source code"
    echo "Run 'jupyter notebook' to start Jupyter with model_checker available"
  '';
}