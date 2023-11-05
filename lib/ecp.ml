(* Elliptic Curve Pairings *)

open Misc

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
end

module type CURVE = sig
  module Fr : sig
    include Field.S
    include G with type t := t and type fr := t
    val ( ** ) : t -> Z.t -> t
    val gen : t Gen.t
  end
  module G1 : G with type fr := Fr.t
  module G2 : G with type fr := Fr.t
  module GT : G with type fr := Fr.t
  module Pairing : sig
    val pairing : G1.t -> G2.t -> GT.t
  end
end

module Bls12_381 = struct

  (* extend Bls12_381 with some printers *)
  include Bls12_381

  module Fr = struct
    module Fr = struct
      include Fr
      let pp ppf fr = Z.pp_print ppf (to_z fr)
      let (~-) = negate
      let ( - ) x y = x + ~- y
      let equal = eq
      let of_q q = of_z q.Q.num / of_z q.Q.den
      let sum = List.fold_left (+) zero
      let gen rng = random ~state:rng ()
      let of_Fr = Fun.id
    end
    include Fr
    module Poly = struct
      include Polynomial.Make(Fr)
      let of_q : Polynomial.Make(Q).t -> t = List.map Fr.of_q
    end
  end

  module type G = G with type fr = Fr.t

  module ExtendG( G : sig
      type t
      val to_bytes : t -> bytes
      val add : t -> t -> t
      val mul : t -> Fr.t -> t
      val negate : t -> t
      val eq : t -> t -> bool
      val zero : t
      val one : t
    end ) = struct
    include G
    let pp ppf g1 = Hex.pp ppf (Hex.of_bytes (to_bytes g1))
    let ( + ) = add
    let ( ~- ) = negate
    let ( - ) x y = x + ~- y
    let ( * ) = mul
    let ( = ) = eq
    let sum = List.fold_left (+) zero
    let of_Fr = ( * ) one
    let of_q q = of_Fr Fr.(of_z q.Q.num / of_z q.Q.den)
  end

  module G1 = struct
    include G1
    include ExtendG(G1)
  end

  module G2 = struct
    include G2
    include ExtendG(G2)
  end

  module GT = struct
    include GT
    include ExtendG(GT)
  end
end

(* (g^i)^j = g^i * j *)
let () =
  let open Bls12_381 in
  let rng = Random.State.make_self_init () in
  let gen rng = Random.State.int rng 10000 in
  let fr = Fr.of_int in
  let a = gen rng in
  let g_of_int x = G1.of_Fr @@ fr x in
  (* g^a = g * a  =  of_Fr a *)
  assert (G1.(eq (one * Fr.of_int a) (g_of_int a)));
  let b = gen rng in
  let c = gen rng in
  let d = gen rng in
  (* g^(ab + cd) *)
  assert (G1.(eq
                (one * Fr.(fr a * fr b + fr c * fr d))
                (one * Fr.(fr a * fr b) + one * Fr.(fr c * fr d))))
