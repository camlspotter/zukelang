open Misclib

module type G = sig
  type t
  type fr
  val zero : t
  val one : t
  val ( ~- ) : t -> t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> fr -> t
  val ( = ) : t -> t -> bool
  val sum : t list -> t
  val of_Fr : fr -> t
  val of_q : Q.t -> t
  val pp : t printer

  val sum_map : 'a Var.Map.t -> (Var.t -> 'a -> t) -> t
  (** $\Sigma_{k\in Dom(m)} f k mk$ *)

  val dot : t Var.Map.t -> fr Var.Map.t -> t
  (** $\Sigma_{k\in Dom(m)} mk \cdot ck$ *)

  val powers : int -> fr -> t list
  (** $\{ g^s^i \}_{i\in[d]}$ *)

  val apply_powers : fr Polynomial.t -> t list -> t
  (** $\Sigma_i c_i x^i$ *)

  include JSON.Conv.S with type t := t
end

module type S = sig
  module Fr : sig
    include Field.COMPARABLE
    include G with type t := t and type fr := t
    val ( ** ) : t -> Z.t -> t
    val gen : t Gen.t
    module Poly : Polynomial.S with type f = t
    val order : Z.t
  end
  module G1 : G with type fr := Fr.t
  module G2 : G with type fr := Fr.t
  module GT : G with type fr := Fr.t
  module Pairing : sig
    val pairing : G1.t -> G2.t -> GT.t
  end
end

module Bls12_381 : S
  with type Fr.t = Bls12_381.Fr.t
  and type G1.t = Bls12_381.G1.t
  and type G2.t = Bls12_381.G2.t
  and type GT.t = Bls12_381.GT.t

module Root_of_unity(F : sig
    include Field.S
    val ( ** ) : t -> Z.t -> t
    val order : Z.t
  end) : sig

  (* [f_of_uint base x] computes the [F.t] value for $x$ of [base] bit uint *)
  val f_of_uint : int -> int -> F.t option

end
