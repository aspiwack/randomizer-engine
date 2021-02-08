# Update Opam deps:
# $ opam2nix resolve --ocaml-version 4.11.1 ./randomizer-engine.opam

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
    pkgs.niv
    opam2nix
  ];
}
