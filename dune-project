(lang dune 2.7)
(name fpm)
(version 0.0.1)

(generate_opam_files true)

(source (github felixmoebius/fpm))
(authors "Felix Moebius")

(package
 (name fpm)
 (synopsis "Felix Proof Machine")
 (depends
  (dune (>= 2.7.1))
  (base (>= v0.14.0))
  (stdio (>= v0.14.0))
  (ppx_expect (>= v0.14.0))))