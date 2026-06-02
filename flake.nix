{
  description = "ModelChecker — Z3-based bimodal logic oracle";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      python = pkgs.python312;
    in
    {
      devShells.${system}.default = pkgs.mkShell {
        packages = [
          (python.withPackages (ps: with ps; [
            z3-solver
            pytest
            pytest-cov
          ]))
        ];

        BIMODAL_HARNESS_SRC_DEFAULT = "../BimodalHarness/src";

        shellHook = ''
          MC_SRC="$PWD/code/src"
          BH_SRC="''${BIMODAL_HARNESS_SRC:-$BIMODAL_HARNESS_SRC_DEFAULT}"

          if [ -d "$BH_SRC/bimodal_harness" ]; then
            export PYTHONPATH="$MC_SRC:$BH_SRC''${PYTHONPATH:+:$PYTHONPATH}"
            echo "[devShell] BimodalHarness: $BH_SRC"
          else
            export PYTHONPATH="$MC_SRC''${PYTHONPATH:+:$PYTHONPATH}"
            echo "[devShell] WARNING: BimodalHarness not found at $BH_SRC"
            echo "  Clone as sibling or set BIMODAL_HARNESS_SRC=/path/to/BimodalHarness/src"
          fi
        '';
      };
    };
}
