{
  description = "contract2game";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    systems.url = "github:nix-systems/default";
    act.url = "github:ethereum/act";
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.systems.follows = "systems";
    };
  };

  outputs = { self, flake-utils, nixpkgs, act, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { system = system; };
        contract2game = pkgs.python3.pkgs.buildPythonApplication rec {
          pname = "contract2game";
          version = "0.0.1";
          pyproject = true;
          src = ./.;
          propagatedBuildInputs = with pkgs.python3.pkgs; [ z3 setuptools ];
          nativeBuildInputs = with pkgs.python3.pkgs; [
            setuptools
            wheel
          ];
        };
      in rec {
        packages.contract2game = contract2game;
        packages.default = packages.contract2game;
        devShell = pkgs.mkShell {
          packages = [
            act.packages.${system}.default
            (pkgs.python3.withPackages (ps: with ps; [z3 setuptools]))
          ];
        };
      });
}
