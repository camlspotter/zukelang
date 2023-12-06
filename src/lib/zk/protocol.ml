open Misclib

module type S = sig
  type f

  type circuit

  type qap

  type pkey [@@deriving yojson]

  type vkey [@@deriving yojson]

  type proof [@@deriving yojson]

  val keygen : Gen.rng -> circuit -> qap -> pkey * vkey

  val prove : Gen.rng -> qap -> pkey -> f Var.Map.t -> proof

  val verify : f Var.Map.t -> vkey -> proof -> bool
end
