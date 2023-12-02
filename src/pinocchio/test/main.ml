open Zk

module C = Curve.Bls12_381
module F = Curve.Bls12_381.Fr
module Pinocchio = Pinocchio.Make(C)
module Test = Protocol.Test_suites(F)(Pinocchio.ZK)
