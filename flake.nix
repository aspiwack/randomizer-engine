{
  nixConfig = {
    # Why ever must I specify the extra-substituters from
    # tweag/topiary? They ought to be transitively imported, don't
    # they?
    extra-substituters = [
      "https://aspiwack.cachix.org"
      "https://tweag-topiary.cachix.org"
    ];
    extra-trusted-public-keys = [
      "aspiwack.cachix.org-1:2D/Nc4rGV10LY8O+c3HMbOJ4wtMY6w7xFubjEmexcfc="
      "tweag-topiary.cachix.org-1:8TKqya43LAfj4qNHnljLpuBnxAY/YwEBfzo3kzXxNY0="
    ];
  };

  inputs = {
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.follows = "opam-nix/nixpkgs";
    topiary.url = "github:tweag/topiary";
    pre-commit-hooks.url = "github:cachix/pre-commit-hooks.nix";
  };

  outputs = { self, flake-utils, opam-nix, nixpkgs, topiary, pre-commit-hooks }@inputs:
    let package = "randomizer-engine";
    in flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        on = opam-nix.lib.${system};
        devPackagesQuery = {
          # You can add "development" packages here. They will get added to the devShell automatically.
          ocaml-lsp-server = "*";
        };
        query = devPackagesQuery // {
          ## You can force versions of certain packages here, e.g:
          ## - force the ocaml compiler to be taken from opam-repository:
          ocaml-base-compiler = "*";
          ## - or force the compiler to be taken from nixpkgs and be a certain version:
          # ocaml-system = "4.14.0";
          ## - or force ocamlfind to be a certain version:
          # ocamlfind = "1.9.2";
        };
        scope = on.buildOpamProject' { } ./. query;
        overlay = final: prev: {
          # You can add overrides here
          ${package} = prev.${package}.overrideAttrs (_: {
            # Prevent the ocaml dependencies from leaking into dependent environments
            doNixSupport = false;
          });
        };
        scope' = scope.overrideScope' overlay;
        # The main package containing the executable
        main = scope'.${package};
        # Packages from devPackagesQuery
        devPackages = builtins.attrValues
          (pkgs.lib.getAttrs (builtins.attrNames devPackagesQuery) scope');
        precommit = pre-commit-hooks.lib.${system}.run {
            src = ./.;
            hooks = {
              topiary = pkgs.lib.mkForce (topiary.lib.${system}.pre-commit-hook);
            };
        };
      in {
        legacyPackages = scope';

        packages.default = main;

        devShells.default = pkgs.mkShell {
          inputsFrom = [ main ];
          buildInputs = devPackages ++ [
            # You can add packages from nixpkgs here

            # can be invoked with $ git ls-files | grep -e '\.ml\(i\)\?$' | xargs -n1 topiary -i -f
            # Below is probably the right way to do when stable for
            #   now let's call the flake directly.
            # pkgs.topiary
            topiary.packages.${system}.default
          ];

          # sets up the pre-commit hooks upon entering the dev shell
          inherit (precommit) shellHook;
        };
      });
}
