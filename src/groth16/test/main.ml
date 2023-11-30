open Zk

module C = Ecp.Bls12_381
module F = Ecp.Bls12_381.Fr
module Lang = Lang.Make(F)
module Groth16 = Groth16.Make(C)
module Test = Protocol.Test(F)(Groth16)

open Lang.Expr.Combinator

let () =
  Test.random_test @@
  let_ (input "input" secret ty_field) (fun x -> if_ (x == !0) !1 !2)

(* $ONE is not used

   gates: v9 = v8 * v8.   No $ONE occurs.

   input_public must be empty!
*)
let () =
  Test.random_test @@
  let_ (input "input" secret ty_field) (fun x -> x * x)

(* simple pair *)
let () =
  Test.random_test @@
  let_ (input "input" secret ty_field) (fun x -> (pair (x + !1) (x * x)))
