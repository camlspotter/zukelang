open Misc

module Make(F : Field.COMPARABLE) : sig

  val one : Var.t
  (** Special variable for constants.  For example, 2 is encoded
      as 2 * one  in the circuit.
  *)

  val out : Var.t
  (** The special variable for the output *)

  module Gate : sig
    (** $\Sigma_{k} c_k x_k$  where $x_0 = \mathtt{one}$ *)
    type affine = F.t Var.Map.t
    val pp_affine : affine printer
    val compare_affine : affine comparator

    (** z + 3 = (2y + 3one) * (3z + 4w + 6one) *)
    type gate = { lhs: affine; l: affine; r: affine }

    type t = gate

    val pp : gate printer

    val compare : gate comparator

    module Set : sig
      include Set.S with type elt = gate
      val pp : t printer
    end
  end

  type circuit =
    { gates : Gate.Set.t; (** Gates with the output variables *)
      input : Var.Set.t;
      output : Var.Set.t;
      mids : Var.Set.t; (** Intermediate variables *)
    }

  type t = circuit

  val pp : t printer

  val vars : Gate.Set.t -> Var.Set.t

  val ios : t -> Var.Set.t

  val eval : F.t Var.Map.t -> Gate.Set.t -> (F.t Var.Map.t, F.t Var.Map.t) result

  val of_expr : Lang.Make(F).Expr.t -> t

  val test : unit -> unit
end
