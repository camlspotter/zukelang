(lang dune 3.2)

(name zukelang)

(generate_opam_files true)

(package
 (name zukelang)
 (synopsis "A ZK language")
 (description "A ZK language")
 (depends zarith bls12-381 unix ppx_yojson_conv_lib hex ppxlib.metaquot))

