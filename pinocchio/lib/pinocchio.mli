open Utils

module Make(C : Ecp.CURVE) : sig
  type circuit = Circuit.Make(C.Fr).t
  type qap = QAP.Make(C.Fr).t

  type ekey [@@deriving yojson] (** Evaluation key *)

  type vkey [@@deriving yojson] (** Verificaiton key *)

  type proof [@@deriving yojson]

  module NonZK : sig
    val keygen : circuit -> qap -> ekey * vkey
    (** Key generation *)

    val output_of_solution : circuit -> C.Fr.t Var.Map.t -> C.Fr.t Var.Map.t
    (** The output of the solution *)

    val prove : qap -> ekey -> C.Fr.t Var.Map.t -> proof
    (** Obtain a proof of the computation *)

    val verify : C.Fr.t Var.Map.t -> vkey -> proof -> bool
    (** Verify the computation proof *)
  end

  module ZK : sig
    val keygen : circuit -> qap -> ekey * vkey
    (** Key generation *)

    val output_of_solution : circuit -> C.Fr.t Var.Map.t -> C.Fr.t Var.Map.t
    (** The output of the solution *)

    val prove : qap -> ekey -> C.Fr.t Var.Map.t -> proof
    (** Obtain a proof of the computation *)

    val verify : C.Fr.t Var.Map.t -> vkey -> proof -> bool
    (** Verify the computation proof *)
  end
end
