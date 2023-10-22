(* Learning Bls12-381 *)

module Bls12_381 = struct
  (* extend Bls12_381 with some printers *)
  include Bls12_381

  module Fr = struct
    include Fr

    let pp ppf fr = Z.pp_print ppf (to_z fr)
  end

  module G1 = struct
    include G1

    let pp ppf g1 =
      Hex.pp ppf (Hex.of_bytes (G1.to_bytes g1))
  end

  module G2 = struct
    include G2

    let pp ppf g2 =
      Hex.pp ppf (Hex.of_bytes (G2.to_bytes g2))
  end
end

(* Pairing check *)
let state = Random.State.make [||]

(* https://medium.com/@VitalikButerin/exploring-elliptic-curve-pairings-c73c1864e627 *)
let test_pairing () =
  let open Bls12_381 in
  Format.eprintf "#Fr: %a@." Z.pp_print Fr.order ;
  (* Fq12 is NOT Fq.  It is much much larger than Fq.
     Fq is hidden in Bls12-381.
  *)
  Format.eprintf "#Fq12: %a@." Z.pp_print Fq12.order ;
  (* G1 : curve built over the field [Fq]
     I believe Bls12_381 does NOT provide a way to decode a G1 point to Fq.t * Fq.t
     Bytes encoding of G1 point is in little endian.
  *)
  Format.eprintf "G1.zero: %a@." G1.pp G1.zero ;
  Format.eprintf "G1.one: %a@." G1.pp G1.one ;
  (* val G1.mul : G1.t -> Fr.t -> G1.t *)
  let g1_123 = G1.(mul one (Fr.of_z (Z.of_int 123))) in
  Format.eprintf "G1.123: %a@." G1.pp g1_123 ;
  (* G2 : curve built over the field [Fq^2]
     I believe Bls12_381 does NOT provide a way to decode a G1 point to Fq.t * Fq.t
     Bytes encoding of G2 point is in little endian.
  *)
  Format.eprintf "G2.zero: %a@." G2.pp G2.zero ;
  Format.eprintf "G2.one: %a@." G2.pp G2.one ;

  (* k : toxic waste.  It must not be known to ANYONE *)
  let k = Fr.random ~state () in
  Format.eprintf "k: %a@." Fr.pp k ;

  (* P and Q are open *)
  let (_P : G1.t), (_Q : G2.t) =
    let p = Fr.random ~state () in
    (* (P,Q) where Q = P * k *)
    let _P = G1.mul G1.one p in
    let _Q = G2.mul (G2.mul G2.one k) p in
    (_P, _Q)
  in

  (* Once _Q is computed, k must be discarded immediately *)

  (* r : only the prover knows it *)
  let r = Fr.random ~state () in
  (* (R,S) = (P * r, Q * r) *)
  let (_R : G1.t), (_S : G2.t) = (G1.mul _P r, G2.mul _Q r) in
  let verify (_P, _Q) (_R, _S) =
    (* Verifier checks that the prover knows some r such that
         _P * r = _R
       but without knowing what r is
    *)
    (* e(P, S) = e(R, Q), since
       e(P, Q * r) = e(P * r, Q) = e(R, Q)
    *)
    let gt1 = Pairing.pairing _P _S in
    let gt2 = Pairing.pairing _R _Q in
    assert (GT.eq gt1 gt2) ;
    (* e(P, S) = e(R, Q) <=> e(P, S) / e(R, Q) = 1
                         <=> e(P, S) * e(R, Q)^(-1) = 1
                         <=> e(P, S) * e(R, -Q) = 1
    *)
    assert (Pairing.pairing_check [(_P, _S); (_R, G2.negate _Q)])
  in
  verify (_P, _Q) (_R, _S) ;
  prerr_endline "Pairing check done" ;

  (* If k is known to the prover, he can build (R, S) such that S = R * k
     without knowing r such that P * r = R
  *)
  let fake_R, fake_S =
    let r = Fr.random ~state () in
    let fake_R = G1.mul G1.one r in
    let fake_S = G2.mul G2.one Fr.(r * k) in
    (fake_R, fake_S)
  in
  verify (_P, _Q) (fake_R, fake_S) ;
  prerr_endline "Fake pairing check done"

(* https://qiita.com/herumi/items/e69721380278c5a30d01 *)
let test_signing () =
  let open Bls12_381 in
  (* public key signing *)
  prerr_endline "public key signing" ;

  (* Why _Q should not be just G2.one ? *)
  let _Q = G2.random ~state () in
  (* secret key *)
  let sk = Fr.random ~state () in
  (* public key: G2 * sk *)
  let pk = G2.mul _Q sk in
  (* hash of a message *)
  let hash = G1.random ~state () in
  (* signature: hash * sk *)
  let sg = G1.mul hash sk in
  let verify pk hash sg =
    (* e(hash, pk) = e(hash, Q * sk) = e(hash * sk, Q) = e(sg, Q) *)
    assert (GT.eq (Pairing.pairing hash pk) (Pairing.pairing sg _Q)) ;
    assert (Pairing.pairing_check [(hash, pk); (sg, G2.negate _Q)])
  in
  verify pk hash sg ;
  prerr_endline "public key signing done"

let test () =
  test_pairing () ;
  test_signing ()
