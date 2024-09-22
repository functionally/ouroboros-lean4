{

  description = "Peras";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    lean = {
      url = "github:leanprover/lean4?ref=v4.7.0";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  # elan.url = "github:leanprover/elan";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, lean, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      leanPkgs = lean.packages.${system};
      praos = leanPkgs.buildLeanPackage {
        name = "Praos";
        src = ./praos/src;
      };
      peras = leanPkgs.buildLeanPackage {
        name = "Peras";
        src = ./peras/src;
      };
      leios = leanPkgs.buildLeanPackage {
        name = "Leios";
        src = ./leios/src;
      };
    in {
      packages =
        praos //
        peras //
        leios //
        { inherit (leanPkgs) lean; }
      ;
      devShell = pkgs.mkShell {
        buildInputs = [
          pkgs.lean4
          pkgs.elan
        ];
      };
      defaultPackage = peras.modRoot;
    });

  nixConfig = {
    bash-prompt = "[lean4:\\w]$ ";
  };

}
