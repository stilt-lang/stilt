(lang dune 3.24)

(using menhir 3.0)

(name stilt-ref)

(generate_opam_files true)

(license "MIT OR Apache-2.0")

(authors "The Stilt Project Contributors")

(maintainers "The Stilt Project Contributors")

(package
 (name stilt-ref)
 (synopsis "The reference interpreter for Stilt")
 (description
  "stilt-ref defines the observable behaviour of Stilt programs. Every other implementation is tested against it.")
 (depends
  (ocaml
   (>= 5.5))
  (cmdliner
   (>= 2.1))
  (menhir
   (>= 20260209))
  (ppx_expect
   (and
    :with-test
    (>= v0.17)))
  (ocamlformat
   (and
    :with-dev-setup
    (= 0.29.0)))
  ; The playground's interpreter, compiled to JavaScript (playground/README.md).
  (js_of_ocaml
   (and
    :with-dev-setup
    (= 6.5.0)))
  (js_of_ocaml-compiler
   (and
    :with-dev-setup
    (= 6.5.0)))))
