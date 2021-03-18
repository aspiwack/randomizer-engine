# Update Opam deps:
# $ opam2nix resolve --ocaml-version 4.11.1 ./randomizer-engine.opam ocp-indent ocaml-lsp-server utop

{ sources ? import ./nix/sources.nix }:
let
  niv-overlay = _: pkgs: { niv = (import sources.niv {}).niv;};
  pkgs = import sources.nixpkgs { overlays = [ niv-overlay ] ; config = {}; };
  opam2nix = import sources.opam2nix {};
  ocaml = pkgs.ocaml-ng.ocamlPackages_4_11.ocaml;
  selection = opam2nix.build {
    inherit ocaml;
    selection = ./opam-selection.nix;
    src = ./.;
  };
in
pkgs.mkShell {
  inputsFrom = [
    selection.randomizer-engine
  ];
  buildInputs = [
    # Ocaml dev tools
    # XXX: there currently some duplication here. But we can remove
    # the need from passing any of this manually to `opam2nix` and
    # possibly share factor these dependencies, using the
    # opam2nix.resolve Nix function see the documentation of opam2nix,
    # as well as the dev-tool example.
    selection.ocp-indent
    selection.ocaml-lsp-server
    # XXX: utop doesn't build because of some system dependency
    # thingy. I'll see later.
    # selection.utop

    # Nix management
    pkgs.niv
    opam2nix
  ];
}
