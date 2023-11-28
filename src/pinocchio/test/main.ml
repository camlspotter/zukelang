open Math

module C = Ecp.Bls12_381
module F = Ecp.Bls12_381.Fr
module Lang = Lang.Make(F)
module Pinocchio = Pinocchio.Make(C)
module Test = Protocol.Test(F)(Pinocchio.ZK)

let () =
  let open Lang.Expr.C in
  let e =
    let x = Var.make "x" in
    let_ x (input secret ty_field) (if_ (var x Lang.Type.Field == !0) !1 !2)
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
    let_ x (input secret ty_field) (var x Lang.Type.Field * var x Lang.Type.Field)
  in
  Test.test e

(* simple pair *)
let () =
  let open Lang.Expr.C in
  let e =
    let x = Var.make "x" in
    let_ x (input secret ty_field) (pair (var x Lang.Type.Field + !1) (var x Lang.Type.Field * var x Lang.Type.Field ))
  in
  Test.test e

(* complex pair

   $ONE in the code, but is gone from the circuit!
*)
let () =
  let open Lang.Expr.C in
  let e =
    let x = Var.make "x" in
    let_ x (input secret ty_field)
    @@ let y = Var.make "y" in
    let_ y (pair (pair (var x ty_field + !1) (var x ty_field * var x ty_field)) (var x ty_field * var x ty_field * var x ty_field))
    @@ snd (fst (var y (ty_pair (ty_pair ty_field ty_field) ty_field)))
  in
  Test.test e
