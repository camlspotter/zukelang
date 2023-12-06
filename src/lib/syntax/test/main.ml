open Syntax

module Trans = Trans.Make(Zk.Curve.Bls12_381.Fr)

let () =
  (* metaquot cannot provide the location of the code. *)
  let loc = Location.none in
  ignore @@ Trans.f [%expr 1 + 1 * 3 + secret "hello"]
