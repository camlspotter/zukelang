(* Elliptic Curve Pairings *)

open Utils

module type CURVE = Bls12_381.CURVE

(* conversion from polynomial ring K[Q] to K[G] *)
module Conv(G : CURVE) : sig
  val of_q : Q.t -> G.t
  val of_qs : Q.t list -> G.t list
end = struct
  let of_q q = G.mul G.one G.Scalar.(of_z q.Q.num / of_z q.Q.den)

  let of_qs = List.map of_q
end

module Poly(G : CURVE) : sig
  type t = G.t list
  val apply : t -> G.Scalar.t -> G.t
end = struct
  type t = G.t list

  let apply f s =
    List.fold_left G.add G.zero
    @@ List.mapi (fun i g -> G.mul g G.Scalar.(s ** Z.of_int i)) f
end

module Bls12_381 = struct
  (* extend Bls12_381 with some printers *)
  include Bls12_381

  module type G = sig
    type t

    val zero : t

    val one : t

    val ( ~- ) : t -> t
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> Fr.t -> t
    val sum : t list -> t

    val ( = ) : t -> t -> bool

    val of_Fr : Fr.t -> t

    val pp : t printer
  end

  module Fr = struct
    module Fr = struct
      include Fr
      let pp ppf fr = Z.pp_print ppf (to_z fr)
      let (~-) = negate
      let ( - ) x y = x + ~- y
      let equal = eq
      let of_q q = of_z q.Q.num / of_z q.Q.den
      let sum = List.fold_left (+) zero
    end
    include Fr
    module Poly = struct
      include Polynomial.Make(Fr)
      let of_q : Polynomial.Make(Q).t -> t = List.map of_q
    end
    module Vec = struct
      type vec = t list
      let imul (v1 : vec) (v2 : vec) : t =
        List.fold_left (fun acc (x1, x2) -> x1 * x2 + acc) zero (List.combine v1 v2)
      type t = vec
    end
    let gen rng = random ~state:rng ()
  end

  module G1 = struct
    include G1
    include Conv(G1)
    type fr = Fr.t
    module Poly = Poly(G1)
    let pp ppf g1 = Hex.pp ppf (Hex.of_bytes (G1.to_bytes g1))
    let ( * ) = mul
    let ( + ) = add
    let ( ~- ) = negate
    let ( - ) x y = x + ~- y
    let ( = ) = eq
    let sum = List.fold_left (+) zero
    let of_Fr = mul one
  end

  module G2 = struct
    include G2
    include Conv(G2)
    type fr = Fr.t
    module Poly = Poly(G2)
    let pp ppf g2 = Hex.pp ppf (Hex.of_bytes (G2.to_bytes g2))
    let ( * ) = mul
    let ( + ) = add
    let ( ~- ) = negate
    let ( - ) x y = x + ~- y
    let ( = ) = eq
    let sum = List.fold_left (+) zero
    let of_Fr = mul one
  end

  module GT = struct
    include GT
    let pp ppf g = Hex.pp ppf (Hex.of_bytes (GT.to_bytes g))
    type fr = Fr.t
    let ( + ) = add
    let ( ~- ) = negate
    let ( - ) x y = x + ~- y
    let ( * ) = mul
    let ( = ) = eq
    let sum = List.fold_left (+) zero
    let of_Fr = mul one
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
