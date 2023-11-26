open Utils

module Make(C : Ecp.CURVE) : sig

  module API : sig
    type circuit = Circuit.Make(C.Fr).circuit

    type qap = QAP.Make(C.Fr).t

    type pkey [@@deriving yojson] (** priving key *)

    type vkey [@@deriving yojson] (** verification key *)

    type proof [@@deriving yojson]

    val keygen : circuit -> qap -> pkey * vkey
    (** Key generation *)

    val prove : qap -> pkey -> C.Fr.t Var.Map.t -> proof
    (** Obtain a proof of the computation *)

    val verify : C.Fr.t Var.Map.t -> vkey -> proof -> bool
    (** Verify the computation proof *)
  end
end
