(* Elliptic Curve Pairings *)

open Misclib
open Ppx_yojson_conv_lib.Yojson_conv

(*
  (* $\{ g^s^i \}_{i\in[d]}$ *)
  let powers (type t) (module G : G with type t = t) d s =
    List.init (d+1) (fun i ->
        let s'i = Fr.(s ** Z.of_int i) in
        i, G.of_Fr s'i)

  (* $\Sigma_i c_i x^i$ *)
  let apply_powers (type t) (module G : G with type t = t) (cs : Poly.t) xis =
    let open G in
    sum @@
    List.mapi (fun i c ->
        let xi = List.assoc i xis in
        xi * c) cs
*)

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

module type CURVE = sig
  module Fr : sig
    include Field.COMPARABLE
    include G with type t := t and type fr := t
    val ( ** ) : t -> Z.t -> t
    val gen : t Gen.t
    module Poly : Polynomial.S with type f = t
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

  module ExtendMap(G : sig
      type t
      type fr
      val (+) : t -> t -> t
      val ( * ) : t -> fr -> t
      val zero : t
      val of_Fr : fr -> t
      val fr_power : fr -> Z.t -> fr
    end ) = struct
    open G

    (* $\Sigma_{k\in Dom(m)} f k mk$ *)
    let sum_map m f = Var.Map.fold (fun k v acc -> f k v + acc) m zero

    (* $\Sigma_{k\in Dom(m)} mk \cdot ck$ *)
    let dot m c =
      let open Var.Infix in
      if not (Var.Set.equal (Var.Map.domain m) (Var.Map.domain c)) then begin
        prerr_endline "Domain mismatch";
        Format.(ef "m : %a@.c : %a@." Var.Set.pp (Var.Map.domain m) Var.Set.pp (Var.Map.domain c));
        assert false
      end;
      sum_map m (fun k mk ->
          let ck = c #! k in
          mk * ck)

    (* $\{ g^s^i \}_{i\in[d]}$ *)
    let powers d s =
      List.init Stdlib.(d+1) (fun i ->
          let s'i = fr_power s (Z.of_int i) in
          of_Fr s'i)

    (* $\Sigma_i c_i x^i$ *)
    let apply_powers (cs : fr Polynomial.t) xis =
      let rec loop acc = function
        | c::cs, x::xis -> loop (x * c + acc) (cs, xis)
        | [], _ -> acc
        | _, [] -> invalid_arg "apply_powers"
      in
      loop zero (cs, xis)
  end

  module Fr = struct
    module Fr = struct
      include Fr
      let pp ppf fr =
        let z = to_z fr in
        let z =
          if Z.(z > Fr.order - of_int 1_000_000) then
            Z.(z - Fr.order)
          else z
        in
        Z.pp_print ppf z
      let (~-) = negate
      let ( - ) x y = x + ~- y
      let equal = eq
      let of_q q = of_z q.Q.num / of_z q.Q.den
      let sum = List.fold_left (+) zero
      let gen rng = random ~state:rng ()
      let of_Fr = Fun.id

      let yojson_of_t f = Z.yojson_of_t @@ Fr.to_z f
      let t_of_yojson j = Fr.of_z @@ Z.t_of_yojson j
    end
    include Fr
    module Poly = struct
      include Polynomial.Make(Fr)
      let of_q : Polynomial.Make(Q).t -> t = List.map Fr.of_q
    end

    include ExtendMap(struct
        include Fr
        type fr = Fr.t
        let fr_power = ( ** )
      end)
  end

  module type G = G with type fr = Fr.t

  module ExtendG( G : sig
      type t
      val to_bytes : t -> bytes
      val of_bytes_opt : bytes -> t option
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

    include ExtendMap(struct
        include G
        type fr = Fr.t
        let ( + ) = add
        let ( * ) = mul
        let of_Fr = of_Fr
        let fr_power = Fr.( ** )
      end)
  end

  type _bytes = bytes [@@deriving yojson]

  module G1 = struct
    include G1
    include ExtendG(G1)

    let yojson_of_t g = JSON.Conv.yojson_of_bytes @@ to_compressed_bytes g

    let t_of_yojson j = of_compressed_bytes_exn @@ JSON.Conv.bytes_of_yojson j
  end

  module G2 = struct
    include G2
    include ExtendG(G2)

    let yojson_of_t g = JSON.Conv.yojson_of_bytes @@ to_compressed_bytes g

    let t_of_yojson j = of_compressed_bytes_exn @@ JSON.Conv.bytes_of_yojson j
  end

  module GT = struct
    include GT
    include ExtendG(GT)

    let yojson_of_t g = JSON.Conv.yojson_of_bytes @@ to_bytes g

    let t_of_yojson j = of_bytes_exn @@ JSON.Conv.bytes_of_yojson j
  end
end

(* (g^i)^j = g^i * j *)
let () =
  let open Bls12_381 in
  let rng = Gen.init_auto () in
  let gen = Gen.int 10000 in
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
