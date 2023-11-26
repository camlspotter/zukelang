(* https://www.zeroknowledgeblog.com/index.php/groth16 *)

open Utils

module Make(C : Ecp.CURVE) = struct
  open C

  module Base = struct
    module Circuit = Circuit.Make(Fr)

    module Poly = Fr.Poly

    module type G = Ecp.G with type fr := Fr.t

    module QAP = QAP.Make(Fr)

    open Var.Infix

    let g1 = G1.of_Fr

    let g2 = G2.of_Fr

    type pkey =
      { a       : G1.t;               (* α *)
        d1      : G1.t;               (* δ *)
        ti1     : G1.t list;          (* 1, τ, τ^2, τ^3, ..., τ^{n-1} *)
        ltd_mid : G1.t Var.Map.t;     (* {Li(τ)/δ} for i∈[l+1..m] *)
        tiztd   : G1.t list;          (* Z(τ)/δ, τ*Z(τ)/δ, τ^2*Z(τ)/δ, ..., τ^(n-2)*Z(τ)/δ *)
        b1      : G1.t;               (* β not documented but required to compute proof C *)
        b2      : G2.t;               (* β *)
        d2      : G2.t;               (* δ *)
        ti2     : G2.t list           (* 1, τ, τ2, τ3, ..., τn-1 *)
      } [@@deriving yojson]

    type vkey =
      { one1     : G1.t;             (* g^1 *)
        ltgm_io  : G1.t Var.Map.t;   (* {Li(τ)/γ} for i∈[0..l] *)
        one2     : G2.t;             (* g^1 *)
        gm       : G2.t;             (* γ *)
        d        : G2.t;             (* δ *)
        ab       : GT.t              (* αβ *)
      } [@@deriving yojson]

    let setup rng v_io v_mid n (qap : QAP.t) =
      (* Coefficient variables

         - v_io  : [k_0..k_l], public
         - v_mid : [k_{l+1}..k_m], hidden from the verifier
      *)
      let a (* α *)  = Fr.gen rng in
      let b (* β *)  = Fr.gen rng in
      let gm (* γ *) = Fr.gen rng in
      let d (* δ *)  = Fr.gen rng in
      let t (* τ *)  = Fr.gen rng in

      let z (* Z(x) *) = qap.target in

      let l (* Li(X) = β *Ai(X) + α * Bi(X) + Ci(X) *) =
        let pA = qap.v in
        let pB = qap.w in
        let pC = qap.y in
        Var.Map.mapi (fun i pa ->
            let pb = pB #! i in
            let pc = pC #! i in
            let open Poly.Infix in
            b *$ pa + a *$ pb + pc) pA
      in

      let pkey =
        let a (* α *) = g1 a
        and d1 (* δ *) = g1 d
        and ti1 (* {τ^i} *) = G1.powers (n+1) t
        and ltd_mid =
          (* Ll+1(τ)/δ, Ll+2(τ)/δ, ..., Lm(τ)/δ *)
          (* v_mid carries [l+1..m] vars *)
          Var.Map.map (fun lk (* Lk(x) *) ->
              g1 Fr.(Poly.apply lk t / d) (* Lk(τ)/δ *)
            ) @@ Var.Map.filter (fun v _ -> Var.Set.mem v v_mid) l
        and tiztd =
          (* {τ^i*Z(τ)/δ} i∈ [0,n-2] *)
          let ztd (* Z(τ)/δ *) = Fr.(Poly.apply z t / d) in
          List.init (n-1) (fun i -> g1 Fr.((t ** Z.of_int i) * ztd))
        and b1 (* β *) = g1 b
        and b2 (* β *) = g2 b
        and d2 (* δ *) = g2 d
        and ti2 (* {τ^i} *) = G2.powers (n+1) t
        in
        { a; d1; ti1; ltd_mid; tiztd; b1; b2; d2; ti2 }
      in

      let vkey =
        let one1 (* g^1 *) = G1.one
        and ltgm_io =
          (* {Li(τ)/γ} i∈[0..l] *)
          (* v_io carries [0..l] vars *)
          Var.Map.map (fun lk ->
              g1 Fr.(Poly.apply lk t / gm)
            ) @@ Var.Map.filter (fun v _ -> Var.Set.mem v v_io) l
        and one2 (* g^1 *)  = G2.one
        and gm   (* γ *)   = g2 gm
        and d    (* δ *)   = g2 d
        and ab   (* αβ *) = Pairing.pairing (g1 a) (g2 b)
        in
        { one1; ltgm_io; one2; gm; d; ab }
      in

      pkey, vkey

    type proof =
      { a : G1.t;
        b : G2.t;
        c : G1.t
      } [@@deriving yojson]

    let sum_apply_powers (type t) (module G : G with type t = t) ti ps w =
      Var.Map.fold (fun k wk acc ->
          let open G in
          let p = ps #! k in
          G.apply_powers p ti * wk
          + acc) w G.zero

    let prove rng (pkey : pkey) (qap : QAP.t) w (* solution with 1 *) h =
      let r = Fr.gen rng in
      let s = Fr.gen rng in
      let pA (* A *) = qap.v in
      let pB (* B *) = qap.w in
      let a : G1.t (* A *) =
        (* A =  α + w0*A0(τ) + w1*A1(τ) + w2*A2(τ) + w3*A3(τ) + … + wm*Am(τ) + r*δ *)
        let open G1 in
        pkey.a
        + sum_apply_powers (module G1) pkey.ti1 pA w
        + pkey.d1 * r
      in
      let b : G2.t (* B *) =
        (* B =  β + w0*B0(τ) + w1*B1(τ) + w2*B2(τ) + w2*B3(τ) + … + wm*Bm(τ) + s*δ *)
        let open G2 in
        pkey.b2
        + sum_apply_powers (module G2) pkey.ti2 pB w
        + pkey.d2 * s
      in
      let c : G1.t (* C *) =
        (* C = wl+1*(Ll+1(τ)/δ) + … + wm*(Lm(τ)/δ)  +  H(τ)*(Z(τ)/δ)  +  sA  +  rB  -  rsδ
           B = β + w0*B0(τ) + w1*B1(τ) + … + wm*Bm(τ) + sδ *)
        let open G1 in
        let b1 = (* same as above b but of G1 *)
          pkey.b1
          + sum_apply_powers (module G1) pkey.ti1 pB w
          + pkey.d1 * s
        in
        let htztd (* H(τ)*Z(τ)/δ *) = G1.apply_powers h pkey.tiztd in

        (* Σ wk*(Lk(τ)/δ), k∈[l+1..m] *)
        G1.dot pkey.ltd_mid (Var.Map.(restrict (domain pkey.ltd_mid) w))

        + htztd
        + a * s
        + b1 * r
        - pkey.d1 * Fr.(r * s)
      in
      { a; b; c }

    let verify vkey w_io (* public coefficients *) proof =
      (* A * B  =  α * β + Σ wk*Lk(τ)/γ * γ  + C * δ

         - typo in the blog y => γ
      *)
      let e = Pairing.pairing in
      let open GT in
      e proof.a proof.b
      = vkey.ab
        + e (G1.dot vkey.ltgm_io w_io) vkey.gm
        + e proof.c vkey.d

    (* Why the equation holds?

       LHS:

         A * B
          where A =  α + Σwk*Ak(τ) + rδ
            and B =  β + Σwk*Bk(τ) + sδ

         =  αβ + βΣwk*Ak(τ) + αΣwk*Bk(τ) + αsδ + βrδ + (Σwk*Ak(τ))(Σwk*Bk(τ))
            + sδΣwk*Ak(τ) + rδΣwk*Bk(τ) + rsδδ

       RHS:
         α * β + Σio wk*Lk(τ)/γ * γ + C * δ
          where C = Σmid wk*Lk(τ)/δ + H(τ)*(Z(τ)/δ) + sA + rB - rsδ

         = αβ + Σio wk*Lk(τ) + Σmid wk*Lk(τ) + H(τ)*Z(τ) + sδA +rδB - rsδδ
         = αβ + Σwk*Lk(τ) + H(τ)*Z(τ) + sδA +rδB - rsδδ
         = αβ + Σwk*Lk(τ) + H(τ)*Z(τ) + sδA +rδB - rsδδ
             since Li(X) = β *Ai(X) + α * Bi(X) + Ci(X)
                   A =  α + Σwk*Ak(τ) + rδ
                   B =  β + Σwk*Bk(τ) + sδ
         = αβ + βΣwk*Ak(τ) + αΣwk*Bk(τ) + Σwk*C(τ) + H(τ)*Z(τ)
           + sδ (α + Σwk*Ak(τ) + rδ)
           + rδ (β + Σwk*Bk(τ) + sδ)
       - rsδδ
         = αβ + βΣwk*Ak(τ) + αΣwk*Bk(τ) + Σwk*C(τ) + H(τ)*Z(τ)
           + sδα + sδΣwk*Ak(τ) + rsδδ
           + rδβ + rδΣwk*Bk(τ) + rsδδ
       - rsδδ
         = αβ + βΣwk*Ak(τ) + αΣwk*Bk(τ) + Σwk*C(τ) + H(τ)*Z(τ)
           + αsδ + βrδ + sδΣwk*Ak(τ) + rδΣwk*Bk(τ) + rsδδ

       Removing the same sub-terms we get:

         (Σwk*Ak(τ))(Σwk*Bk(τ)) = Σwk*C(τ) + H(τ)*Z(τ)
    *)
  end

  open Base

  type f = Fr.t

  type circuit = Circuit.t

  type qap = QAP.t

  type nonrec pkey = pkey [@@deriving yojson]

  type nonrec vkey = vkey [@@deriving yojson]

  type nonrec proof = proof [@@deriving yojson]

  let keygen rng (circuit : Circuit.t) (qap : QAP.t) =
    let z (* Z(x) *) = qap.target in
    let d = Poly.degree z in
    let ekey, vkey =
      setup rng (Var.Set.union circuit.inputs_public circuit.outputs) circuit.mids d qap
    in
    ekey, vkey

  let prove rng qap pkey sol =
    let _p, h = QAP.eval sol qap in
    prove rng pkey qap sol h

  let verify input_output vkey proof =
    let input_output = Var.Map.add Circuit.one (Fr.of_int 1) input_output in
    verify vkey input_output proof
end
