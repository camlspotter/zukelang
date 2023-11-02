(** QAP triple *)
type 'a vwy = { v : 'a; w : 'a; y : 'a }

module Make(F : Field.S) : sig

  type t =
    { vwy : Polynomial.Make(F).t Var.Map.t vwy;
      target : Polynomial.Make(F).t }

  val build : Circuit.Make(F).Gate.t Var.Map.t -> t * F.t Var.Map.t

  val decompile : t -> F.t Var.Map.t -> ( (Var.t * F.t) list * (Var.t * F.t) list ) Var.Map.t

  val eval : (Var.t * F.t) list -> t -> Polynomial.Make(F).t * Polynomial.Make(F).t
  (** compute $p$ and $h$ *)

  val test : unit -> unit
end
