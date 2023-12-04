module Make(F : Field.COMPARABLE) : sig

  module Polynomial : module type of Polynomial.Make(F)
  module Circuit : module type of Circuit.Make(F)

  type t =
    { v : Polynomial.t Var.Map.t;
      w : Polynomial.t Var.Map.t;
      y : Polynomial.t Var.Map.t;
      target : Polynomial.t }

  val build : Circuit.Gate.Set.t -> t * (int * Circuit.Gate.t) list

  val decompile : t -> (int * Circuit.Gate.t) list -> Circuit.Gate.Set.t

  val eval : F.t Var.Map.t -> t -> Polynomial.t * Polynomial.t
  (** compute $p$ and $h$ *)
end
