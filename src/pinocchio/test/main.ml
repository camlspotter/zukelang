open Zk

module C = Curve.Bls12_381
module F = Curve.Bls12_381.Fr
module Pinocchio = Pinocchio.Make(C)
module Test = Test.Make_suites(F)(Pinocchio.ZK)
