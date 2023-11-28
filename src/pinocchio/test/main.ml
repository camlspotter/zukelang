open Math

module C = Ecp.Bls12_381
module F = Ecp.Bls12_381.Fr
module Lang = Lang.Make(F)
module Pinocchio = Pinocchio.Make(C)
module Test = Protocol.Test(F)(Pinocchio.ZK)

(* I know [x] such that [x^3 + x + 3 = y] *)
let () =
  let open Lang.Expr.C in
  let e =
    let_ (input secret ty_field) (fun x -> x * x * x + x + !3)
  in
  Test.test e

(* if *)
let () =
  let open Lang.Expr.C in
  let e =
    let_ (input secret ty_field) (fun x -> if_ (x == !0) !1 !2)
  in
  Test.test e

(* $ONE is not used

   gates: v9 = v8 * v8.   No $ONE occurs.

   input_public must be empty!
*)
let () =
  let open Lang.Expr.C in
  let e =
    let_ (input secret ty_field) (fun x -> x * x)
  in
  Test.test e

(* simple pair *)
let () =
  let open Lang.Expr.C in
  let e =
    let_ (input secret ty_field) (fun x -> pair (x + !1) (x * x))
  in
  Test.test e

(* complex pair

   $ONE in the code, but is gone from the circuit!
*)
let () =
  let open Lang.Expr.C in
  let e =
    let_ (input secret ty_field) @@ fun x ->
    let_ (pair (pair (x + !1) (x * x)) (x * x * x)) @@ fun y ->
    snd (fst y)
  in
  Test.test e

(* return a bool and complex equal *)
let () =
  let open Lang.Expr.C in
  let e =
    let_ (input secret ty_bool) @@ fun x ->
    let_ (input secret ty_bool) @@ fun y ->
    pair x y == pair y x
  in
  Test.test e

(* either *)
let () =
  let open Lang.Expr.C in
  let e =
    let_ (input secret ty_bool) @@ fun x ->
    if_ x (left x ty_bool) (right ty_bool x)
  in
  Test.test e

(* secret without let *)
let () =
  let open Lang.Expr.C in
  let e = input secret ty_field + !1 in
  Test.test e
