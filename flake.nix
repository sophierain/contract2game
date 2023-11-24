{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    act.url = "github:ethereum/act";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = ins: ins.flake-utils.lib.eachDefaultSystem (system:
    let pkgs = import ins.nixpkgs { inherit system; };
    in {
      devShells.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          (pkgs.python3.withPackages (ps: [ps.z3]))
          ins.act.packages.${system}.default
        ];
      };
    });
}
