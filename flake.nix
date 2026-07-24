{
  description = "ModelChecker — a hyperintensional theorem prover for developing and exploring programmatic semantic theories";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        python = pkgs.python312;

        # nixpkgs builds its Python Z3 bindings from the Z3Prover/z3 source tree under the
        # `z3-solver` attribute name (renamed from the older `z3` attribute) -- this is NOT the
        # PyPI `z3-solver` wheel `code/pyproject.toml` declares as a dependency, it is the
        # nixpkgs-native build with import name `z3` and no PyPI-style dist-info metadata.
        # buildPythonPackage's runtime-dep check would therefore reject it as satisfying the
        # `z3-solver` requirement, so that requirement is relaxed below (see `pythonRelaxDeps`).
        nixZ3 = python.pkgs.z3-solver;

        modelChecker = python.pkgs.buildPythonPackage {
          pname = "model-checker";
          version = "1.3.0";
          pyproject = true;
          src = ./code;

          build-system = [ python.pkgs.setuptools python.pkgs.wheel ];

          # The nixpkgs-native `z3-solver` attribute (see `nixZ3` above) provides the `z3` import
          # but has no PyPI dist-info at all, so it can never satisfy
          # `pythonRuntimeDepsCheckHook`'s post-install metadata check against pyproject.toml's
          # `z3-solver>=4.8.0` requirement (relaxing the version constraint via
          # `pythonRelaxDeps` is not enough -- the hook still looks for *some* installed
          # distribution named `z3-solver`, which will never exist). Strip that single
          # requirement from the built wheel's metadata instead; `networkx` is still checked
          # normally.
          pythonRemoveDeps = [ "z3-solver" ];
          nativeBuildInputs = [ python.pkgs.pythonRelaxDepsHook ];

          propagatedBuildInputs = [
            nixZ3
            python.pkgs.networkx
          ];

          # No test collection during the package build itself; the reproducibility gate is the
          # separate `checks.default` output below (scoped to the known-green bimodal suite).
          doCheck = false;

          pythonImportsCheck = [ "model_checker" "z3" ];

          meta = with pkgs.lib; {
            description = "A hyperintensional theorem prover for developing and exploring programmatic semantic theories";
            homepage = "https://github.com/benbrastmckie/ModelChecker";
            license = licenses.gpl3Plus;
          };
        };

        # BimodalHarness is an optional sibling checkout used only by the oracle differential
        # suite (out of this package's scope, see code/pyproject.toml / task-122 baseline). The
        # dev shell surfaces it on PYTHONPATH when present with no warning/failure branch when
        # absent -- a standalone checkout is a fully supported, unremarkable case.
        bimodalHarnessSrc = "../BimodalHarness/src";

        devPython = python.withPackages (ps: with ps; [
          nixZ3
          setuptools
          pip
          networkx
          pytest
          pytest-xdist
        ]);
      in
      {
        packages.default = modelChecker;

        devShells.default = pkgs.mkShell {
          packages = [ devPython ];

          shellHook = ''
            MC_SRC="$PWD/code/src"
            BH_SRC="''${BIMODAL_HARNESS_SRC:-${bimodalHarnessSrc}}"

            if [ -d "$BH_SRC/bimodal_harness" ]; then
              export PYTHONPATH="$MC_SRC:$BH_SRC''${PYTHONPATH:+:$PYTHONPATH}"
              echo "[devShell] BimodalHarness: $BH_SRC"
            else
              export PYTHONPATH="$MC_SRC''${PYTHONPATH:+:$PYTHONPATH}"
            fi
          '';
        };

        # Scoped to the in-package `theory_lib/bimodal` suite, the reliably-green subset
        # documented in specs/122's RELEASE-BASELINE.md (286/286 passed at `-n 6`, 43.4s
        # wall-clock; `-n auto` is avoided due to a documented CPU-contention flake). The
        # top-level `oracle/` tree is a separate, unpackaged suite (task-118) and the
        # everything-else suite carries 28 documented pre-existing failures unrelated to this
        # flake -- neither belongs in a hermetic hyperintensional reproducibility gate. All
        # Python deps come from nixpkgs; there is no PyPI/network fetch inside the sandbox.
        checks.default = pkgs.stdenv.mkDerivation {
          pname = "model-checker-checks";
          version = "1.3.0";
          src = ./code;

          nativeBuildInputs = [ devPython ];
          dontBuild = true;

          checkPhase = ''
            runHook preCheck
            export PYTHONPATH="$PWD/src"
            export HOME="$TMPDIR"
            pytest src/model_checker/theory_lib/bimodal/tests -n 6 -q
            runHook postCheck
          '';

          doCheck = true;

          installPhase = ''
            mkdir -p $out
            echo "model-checker bimodal suite: green" > $out/result
          '';
        };
      });
}
