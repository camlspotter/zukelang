open Utils

module Make(C : Ecp.CURVE) : sig

  module API : sig
    type circuit

    type qap

    type pkey (** priving key *)

    type vkey (** verification key *)

    type proof

    val compile : secret: Var.Set.t -> Lang.Make(C.Fr).Expr.t -> circuit * qap
    (** Compile an expression to a circuit and a QAP *)

    val keygen : circuit -> qap -> pkey * vkey
    (** Key generation *)

    val solve : circuit -> public: C.Fr.t Var.Map.t -> secret: C.Fr.t Var.Map.t -> C.Fr.t Var.Map.t
    (** Evaluate the circuit with the given input *)

    val output_of_solution : circuit -> C.Fr.t Var.Map.t -> C.Fr.t Var.Map.t
    (** The output of the solution *)

    val prove : qap -> pkey -> C.Fr.t Var.Map.t -> proof
    (** Obtain a proof of the computation *)

    val verify : C.Fr.t Var.Map.t -> vkey -> proof -> bool
    (** Verify the computation proof *)
  end
end
