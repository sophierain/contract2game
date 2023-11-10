{
  description = "contract2game";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    pyproject.url = "github:nix-community/pyproject.nix";
    pyproject.inputs.nixpkgs.follows = "nixpkgs";
    systems.url = "github:nix-systems/default";
    flake-utils.url = "github:numtide/flake-utils";
    flake-utils.inputs.systems.follows = "systems";
    act.url = "github:ethereum/act";
  };

  outputs = { nixpkgs, pyproject, flake-utils, act, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        inherit (nixpkgs) lib;

        pkgs = import nixpkgs { system = system; };
        python = pkgs.python3;

        # parse pyproject.toml
        project = pyproject.lib.project.loadPyproject {
          pyproject = lib.importTOML ./pyproject.toml;
        };
      in
      {
        devShells.default =
          let
            arg = pyproject.lib.renderers.withPackages { inherit python project; };
            pythonEnv = python.withPackages arg;
          in pkgs.mkShell {
            packages = [
              act.packages.${system}.default
              pythonEnv
            ];
          };

        packages.default =
          let attrs = pyproject.lib.renderers.buildPythonPackage { inherit python project; };
          in python.pkgs.buildPythonApplication attrs;
      });
}
