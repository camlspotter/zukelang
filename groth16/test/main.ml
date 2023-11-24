open Utils

include Groth16.Make(Ecp.Bls12_381)

module Lang = Lang.Make(Ecp.Bls12_381.Fr)
module Circuit = Circuit.Make(Ecp.Bls12_381.Fr)

open Ecp.Bls12_381

let test () =

  prerr_endline "PROTOCOL TEST";

  let x = Var.of_string "i" in
  let e =
    let open Lang in
    let open Expr.Infix in
    let x = Expr.Term (Var x) in
    x * x * x + x * !2 + !3
  in

  (* VC *)

  let circuit, qap = API.compile ~secret:(Var.Set.singleton x) e in

  let ekey, vkey = API.keygen circuit qap in

  let public = Var.Map.empty in
  let secret = Var.Map.of_list [x, Fr.of_int 10] in

  let sol = API.solve circuit ~public ~secret in

  let output = API.output_of_solution circuit sol in

  let proof = API.prove qap ekey sol in

  assert (API.verify (Var.Map.concat public output) vkey proof);

  let wrong_output = Var.Map.singleton Circuit.out (Fr.of_int 42) in
  assert (not @@ API.verify (Var.Map.concat public wrong_output) vkey proof);

  prerr_endline "Groth16 test done!"

let () = test ()
