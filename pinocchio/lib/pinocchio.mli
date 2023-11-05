open Utils

module Circuit : sig

  module Make(F : Field.S) : sig

    val one : Var.t
    (** Special variable for constants.  For example, 2 is encoded
        as 2 * one  in the circuit.
    *)

    val out : Var.t
    (** The special variable for the output *)

    module Gate : sig
      type gate = F.t Var.Map.t * F.t Var.Map.t
      (** Multiplication gate.
          Each side of the inputs is a sum of weighted variables.

          Ex.  (2x + 3y + w) * (6x + 0y + 10w)
      *)

      type t = gate

      val pp : t printer
    end

    type circuit =
      { gates : Gate.t Var.Map.t; (** Gates with the output variables *)
        input : Var.Set.t;
        output : Var.Set.t;
        mids : Var.Set.t; (** Intermediate variables *)
      }

    type t = circuit

    val pp : t printer

    val equal_gates : Gate.t Var.Map.t -> Gate.t Var.Map.t -> bool

    val vars : Gate.t Var.Map.t -> Var.Set.t

    val ios : t -> Var.Set.t

    val eval : F.t Var.Map.t -> Gate.t Var.Map.t -> (F.t Var.Map.t, F.t Var.Map.t) result

    val of_expr : Lang.Make(F).Expr.t -> t

    val test : unit -> unit
  end

end

module QAP : sig

  (** QAP triple *)
  type 'a vwy = { v : 'a; w : 'a; y : 'a }

  module Make(F : Field.S) : sig

    type t =
      { vwy : Polynomial.Make(F).t Var.Map.t vwy;
        target : Polynomial.Make(F).t }

    val build : Circuit.Make(F).Gate.t Var.Map.t -> t * F.t Var.Map.t

    val decompile : t -> F.t Var.Map.t -> Circuit.Make(F).Gate.t Var.Map.t

    val eval : F.t Var.Map.t -> t -> Polynomial.Make(F).t * Polynomial.Make(F).t
    (** compute $p$ and $h$ *)

    val test : unit -> unit

  end
end

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
