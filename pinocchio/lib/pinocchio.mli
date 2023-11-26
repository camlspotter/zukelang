open Utils

module Make(C : Ecp.CURVE) : sig
  type circuit = Circuit.Make(C.Fr).t
  type qap = QAP.Make(C.Fr).t

  type pkey [@@deriving yojson] (** Evaluation key *)

  type vkey [@@deriving yojson] (** Verificaiton key *)

  type proof [@@deriving yojson]

  module NonZK : sig
    val keygen : Gen.rng -> circuit -> qap -> pkey * vkey
    (** Key generation *)

    val prove : Gen.rng -> qap -> pkey -> C.Fr.t Var.Map.t -> proof
    (** Obtain a proof of the computation *)

    val verify : C.Fr.t Var.Map.t -> vkey -> proof -> bool
    (** Verify the computation proof *)
  end

  module ZK : sig
    val keygen : Gen.rng -> circuit -> qap -> pkey * vkey
    (** Key generation *)

    val prove : Gen.rng -> qap -> pkey -> C.Fr.t Var.Map.t -> proof
    (** Obtain a proof of the computation *)

    val verify : C.Fr.t Var.Map.t -> vkey -> proof -> bool
    (** Verify the computation proof *)
  end
end
