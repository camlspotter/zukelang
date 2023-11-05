open Utils

module Make(C : Ecp.CURVE) : sig
  type expr = Lang.Make(C.Fr).Expr.t
  type circuit = Circuit.Make(C.Fr).t
  type qap = QAP.Make(C.Fr).t

  type ekey (** Evaluation key *)

  type vkey (** Verificaiton key *)

  type proof

  module NonZK : sig
    val compile : expr -> circuit * qap
    (** Compile an expression to a circuit and a QAP *)

    val keygen : circuit -> qap -> ekey * vkey
    (** Key generation *)

    val solve : circuit -> C.Fr.t Var.Map.t -> C.Fr.t Var.Map.t
    (** Evaluate the circuit with the given input *)

    val output_of_solution : circuit -> C.Fr.t Var.Map.t -> C.Fr.t Var.Map.t
    (** The output of the solution *)

    val prove : qap -> ekey -> C.Fr.t Var.Map.t -> proof
    (** Obtain a proof of the computation *)

    val verify : C.Fr.t Var.Map.t -> vkey -> proof -> bool
    (** Verify the computation proof *)
  end

  module ZK : sig
    val compile : expr -> secret:Var.Set.t -> circuit * qap
    (** Compile an expression to a circuit and a QAP *)

    val keygen : circuit -> qap -> ekey * vkey
    (** Key generation *)

    val solve : circuit -> public:C.Fr.t Var.Map.t -> secret:C.Fr.t Var.Map.t -> C.Fr.t Var.Map.t
    (** Evaluate the circuit with the given input *)

    val output_of_solution : circuit -> C.Fr.t Var.Map.t -> C.Fr.t Var.Map.t
    (** The output of the solution *)

    val prove : qap -> ekey -> C.Fr.t Var.Map.t -> proof
    (** Obtain a proof of the computation *)

    val verify : C.Fr.t Var.Map.t -> vkey -> proof -> bool
    (** Verify the computation proof *)
  end
end

val test : unit -> unit
