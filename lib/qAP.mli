(** QAP triple *)
type 'a vwy = { v : 'a; w : 'a; y : 'a }

module Make(F : Field.COMPARABLE) : sig

  type t =
    { vwy : Polynomial.Make(F).t Var.Map.t vwy;
      target : Polynomial.Make(F).t }

  val build : Circuit.Make(F).Gate.Set.t -> t * (int * Circuit.Make(F).Gate.t) list

  val decompile : t -> (int * Circuit.Make(F).Gate.t) list -> Circuit.Make(F).Gate.Set.t

  val eval : F.t Var.Map.t -> t -> Polynomial.Make(F).t * Polynomial.Make(F).t
  (** compute $p$ and $h$ *)

  val test : unit -> unit
end
