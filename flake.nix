{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    pre-commit-hooks = {
      url = "github:cachix/git-hooks.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, pre-commit-hooks, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        hask = "910";
      in
        {
          checks.pre-commit-check = pre-commit-hooks.lib.${system}.run {
            src = ./.;
            hooks.fourmolu.enable = true;
          };
          devShells.default = pkgs.mkShell {
            inherit (self.checks.${system}.pre-commit-check) shellHook;
            buildInputs = with pkgs; [
              cabal-install
              haskell.compiler."ghc${hask}"
              (haskell-language-server.override { supportedGhcVersions = [ hask ]; })
              fourmolu
            ] ++ (self.checks.${system}.pre-commit-check.enabledPackages);
          };
        }
    );
}
