open Misc

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
