open Utils

val one : Var.t

val out : Var.t

module Gate : sig
  type gate = (Var.t * int) list * (Var.t * int) list

  type t = gate

  val pp : t printer
end

type circuit =
  { gates : Gate.t Var.Map.t;
    mids : Var.Set.t
  }

type t = circuit

include Printable with type t := t

val vars : Gate.t Var.Map.t -> Var.Set.t

val ios : t -> Var.Set.t

val eval : (Var.t * int) list -> Gate.t Var.Map.t -> ((Var.t * int) list, (Var.t * int) list) result

val of_expr : Expr.Expr.expr -> t

val test : unit -> unit
