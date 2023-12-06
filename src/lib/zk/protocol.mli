open Misclib

module type S = sig

  type f
  (** Type of the prime field element *)

  type circuit

  type qap

  type pkey [@@deriving yojson]
  (** Proving key *)

  type vkey [@@deriving yojson]
  (** Verificaiton key *)

  type proof [@@deriving yojson]

  val keygen : Gen.rng -> circuit -> qap -> pkey * vkey
  (** Key generation *)

  val prove : Gen.rng -> qap -> pkey -> f Var.Map.t -> proof
  (** Obtain a proof of the computation *)

  val verify : f Var.Map.t -> vkey -> proof -> bool
  (** Verify the computation proof *)
end
