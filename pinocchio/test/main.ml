open Utils

module C = Ecp.Bls12_381
module F = Ecp.Bls12_381.Fr
module Lang = Lang.Make(F)
module Pinocchio = Pinocchio.Make(C)
module Test = Protocol.Test(F)(Pinocchio.ZK)

let () =
  let open Lang.S in
  let e =
    let x = Lang.var () in
    let_ x (input secret ty_field) (if_ (var x == !0) !1 !2)
  in
  Test.test e
