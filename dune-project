(lang dune 2.7)
(name wiqed)
(version 0.0.1)

(generate_opam_files true)

(source (github felixmoebius/wiqed))
(authors "Felix Moebius")
(maintainers "felix.moebius@posteo.de")

(package
 (name wiqed)
 (synopsis "WIQED Proof Machine")
 (depends
  (dune (>= 2.7.1))
  (base (>= v0.14.0))
  (stdio (>= v0.14.0))
  (ppx_let (>= v0.14.0))
  (ppx_expect (>= v0.14.0))))