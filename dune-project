(lang dune 1.10)
(using menhir 2.0)
(generate_opam_files true)
;; Project description

(name randomizer-engine)
(authors "Arnaud Spiwack")

;; Packages description

(package
  (name randomizer-engine)
  (depends
    (dune :build)
    mlbdd
    oseq
    containers
    msat
    logs
    fmt
    hashcons
    sedlex
    menhir
    (ocp-indent :dev)
    (ocaml-lsp-server :dev)
    (utop :dev)
    ))
