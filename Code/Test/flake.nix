{
  description = "Z3 flake";
  outputs = { self, nixpkgs }: let
    pkgs = nixpkgs.legacyPackages.x86_64-linux;
  in {
    devShell.x86_64-linux = pkgs.mkShell {
      buildInputs = [
        pkgs.python311Packages.z3
        pkgs.python311Packages.setuptools
      ];
    };
  };
}
