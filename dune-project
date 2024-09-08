(lang dune 3.2)

(name zukelang)

(generate_opam_files true)

(source (github camlspotter/zukelang))

(authors "Jun FURUSE <jun.furuse@gmail.com>")

(maintainers "Jun FURUSE <jun.furuse@gmail.com>")

(license MIT)

(package
 (name zukelang)
 (synopsis "A ZK language")
 (description "A ZK language")
 (depends
   (ocaml (>= "4.12.1"))
   dune
   (zarith (>= "1.13"))
   (bls12-381 (= "6.1.0"))
   (ppx_yojson_conv (>= "v0.16.0"))
   ppx_yojson_conv_lib
   hacl-star
   hex
   ppxlib)
 (version "1.0.0"))
