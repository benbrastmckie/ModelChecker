{ pkgs ? import <nixpkgs> {} }:
pkgs.python3Packages.buildPythonPackage {
  pname = "model-checker";
  version = "0.5.13";

  src = ./.;

  # Optional: Specify dependencies
  propagatedBuildInputs = with pkgs.python3Packages; [
    z3-solver
  ];

  meta = with pkgs.lib; {
    description = "A hyperintensional theorem prover for modal, counterfactual conditional, constitutive explanatory, and extensional operators.";
    license = licenses.mit;
    maintainers = [
      {
        name = "Benjamin Brast-McKie";
        email = "benbrastmckie@gmail.com";
      }
      {
        name = "Miguel Buitrago";
        email = "mbuit82@gmail.com";
      }
    ];
  };
}

