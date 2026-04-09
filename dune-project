(lang dune 3.17)

(using menhir 3.0)

(name attack)

(generate_opam_files true)

(authors "Jay Lee <jhlee@ropas.snu.ac.kr>")

(maintainers "Jay Lee <jhlee@ropas.snu.ac.kr>")

(package
 (name attack)
 (synopsis "Attack Static Analyzer")
 (description "Attack static analyzer")
 (depends
   ocaml
   (ocaml-base-compiler
     (= 5.3.0))
   menhir)
 (tags
  ("abstract interpretation" "program analysis")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
