{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  # Include required packages including setuptools for pkg_resources
  buildInputs = with pkgs; [
    python3
    python3Packages.z3
    python3Packages.setuptools  # Provides pkg_resources
    python3Packages.pip
  ];
  
  shellHook = ''
    # Set up local development environment
    export PYTHONPATH="$PWD:$PWD/src:$PYTHONPATH"
    export PATH="$PWD:$PATH"
    
    # Make scripts executable
    chmod +x $PWD/dev_cli.py
    chmod +x $PWD/run_jupyter_demo.py
    chmod +x $PWD/simple_jupyter_test.py
    
    echo "ModelChecker development environment activated"
    echo ""
    echo "To test the model-checker without Jupyter, run:"
    echo "  ./simple_jupyter_test.py"
    echo ""
    echo "If you want to run the interactive notebook, make sure you have"
    echo "all required dependencies and run:"
    echo "  jupyter notebook --no-browser src/model_checker/theory_lib/jupyter/jupyter_demo.ipynb"
  '';
}