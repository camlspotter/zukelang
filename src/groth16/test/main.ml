open Math

module C = Ecp.Bls12_381
module F = Ecp.Bls12_381.Fr
module Lang = Lang.Make(F)
module Groth16 = Groth16.Make(C)
module Test = Protocol.Test(F)(Groth16)

let () =
  let open Lang.Expr.C in
  let e =
    let x = Var.make "x" in
    let_ x (input secret ty_field) (fun x -> if_ (x == !0) !1 !2)
  in
  Test.test e

(* $ONE is not used

   gates: v9 = v8 * v8.   No $ONE occurs.

   input_public must be empty!
*)
let () =
  let open Lang.Expr.C in
  let e =
    let x = Var.make "x" in
    let_ x (input secret ty_field) (fun x -> x * x)
  in
  Test.test e

(* simple pair *)
let () =
  let open Lang.Expr.C in
  let e =
    let x = Var.make "x" in
    let_ x (input secret ty_field) (fun x -> (pair (x + !1) (x * x)))
  in
  Test.test e
