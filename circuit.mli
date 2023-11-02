open Utils

module Make(F : Field.S) : sig

  val one : Var.t

  val out : Var.t

  module Gate : sig
    type gate = (Var.t * F.t) list * (Var.t * F.t) list

    type t = gate

    val pp : t printer
  end

  type circuit =
    { gates : Gate.t Var.Map.t;
      mids : Var.Set.t
    }

  type t = circuit

  val pp : t printer

  val vars : Gate.t Var.Map.t -> Var.Set.t

  val ios : t -> Var.Set.t

  val eval : (Var.t * F.t) list -> Gate.t Var.Map.t -> ((Var.t * F.t) list, (Var.t * F.t) list) result

  val of_expr : Lang.Make(F).Expr.t -> t

  val test : unit -> unit
end
