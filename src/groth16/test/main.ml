open Zk

module C = Curve.Bls12_381
module F = Curve.Bls12_381.Fr
module Groth16 = Groth16.Make(C)
module Test = Test.Make_suites(F)(Groth16)
