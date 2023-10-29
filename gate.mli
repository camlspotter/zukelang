open Utils

type gate = Var.t * (Var.t * int) list * (Var.t * int) list

val pp_gate : gate printer

val pp_gates : gate list printer

type t =
  { gates : gate list;
    mids : Var.Set.t
  }

include Printable with type t := t

val vars : gate list -> Var.Set.t

val eval : (Var.t * int) list -> gate list -> ((Var.t * int) list, (Var.t * int) list) result

val one : Var.t

val out : Var.t

val is_mid : Var.t -> bool

val is_io : Var.t -> bool

val mids : gate list -> Var.t list

val ios : gate list -> Var.t list

val of_expr : Expr.Expr.expr -> gate list

val test : unit -> unit
