open Utils

module PQ = Polynomial.Make(Q)

type 'a vwy = { v : 'a; w : 'a; y : 'a }

let (#!) l k =
  match List.assoc_opt k l with
  | Some res -> res
  | None ->
      Format.ef "Variable %a not found@." Var.pp k;
      assert false

module QAP(F : Field.S) : sig

  type t = (Var.t * F.t Polynomial.t) list vwy * F.t Polynomial.t

  val build : Gate.gate list -> t
  (** compute V, W, Y and a target polynomial t *)

  val eval : (Var.t * int) list -> t -> F.t Polynomial.t * F.t Polynomial.t
  (** compute $p$ and $h$ *)

  val test : unit -> unit

end = struct

  module Poly = Polynomial.Make(F)

  type poly = Poly.t

  type t = (Var.t * poly) list vwy * poly

  let build (gates : Gate.gate list) =
    let rk = List.mapi (fun i (v, _, _) -> v,i) gates in
    let vars = Var.Set.elements @@ Gate.vars gates in
    let v =
      (* $v_k(r_g) = 1$ when gate g has c_k at the left of op *)
      List.map (fun k ->
          (k,
           List.map (fun (g, l, _r) ->
               (g,
                match List.assoc_opt k l with
                | None | Some 0 -> 0
                | Some n -> n)) gates))
        vars
    in

    let w =
      (* $w_k(r_g) = 1$ when gate g has c_k at the right of op *)
      List.map (fun k ->
          (k,
           List.map (fun (g, _l, r) ->
               (g,
                match List.assoc_opt k r with
                | None | Some 0 -> 0
                | Some n -> n)) gates))
        vars
    in

    let y =
      (* $y_k(r_g) = 1$ when gate (v, _, _) , v = c_k *)
      List.map (fun k ->
          (k,
           List.map (fun (g, _l, _r) ->
               (g, if k = g then 1 else 0)) gates)) vars
    in

    List.iter (fun (k, gns) ->
        List.iter (fun (g, n) ->
            Format.ef "v_%a(r_%a) = %d # gate %a has %a in the left arg@."
              Var.pp k
              Var.pp g
              n
              Var.pp g
              Var.pp k) gns) v;
    List.iter (fun (k, gns) ->
        List.iter (fun (g, n) ->
            Format.ef "w_%a(r_%a) = %d # gate %a has %a in the right arg@."
              Var.pp k
              Var.pp g
              n
              Var.pp g
              Var.pp k) gns) w;
    List.iter (fun (k, gns) ->
        List.iter (fun (g, n) ->
            Format.ef "y_%a(r_%a) = %d # gate %a outputs %a@."
              Var.pp k
              Var.pp g
              n
              Var.pp g
              Var.pp k) gns) y;

    let v =
      List.map (fun k ->
          let vk = v #! k in
          let p =
            Poly.interpolate
              (List.map (fun (g, rg) ->
                   let vkrg (* v_k(r_g) *) = vk #! g in
                   F.of_int rg, F.of_int vkrg) rk)
          in
          Format.ef "v_%a(x) = %a@." Var.pp k Poly.pp p;
          k, p
        ) vars
    in

    let w =
      List.map (fun k ->
          let wk = w #! k in
          let p =
            Poly.interpolate
              (List.map (fun (g, rg) ->
                   let wkrg (* w_k(r_g) *) = wk #! g in
                   F.of_int rg, F.of_int wkrg) rk)
          in
          Format.ef "w_%a(x) = %a@." Var.pp k Poly.pp p;
          k, p
        ) vars
    in

    let y =
      List.map (fun k ->
          let yk = y #! k in
          let p =
            Poly.interpolate
              (List.map (fun (g, rg) ->
                   let ykrg (* y_k(r_g) *) = List.assoc g yk in
                   F.of_int rg, F.of_int ykrg) rk)
          in
          Format.ef "y_%a(x) = %a@." Var.pp k Poly.pp p;
          k, p
        ) vars
    in

    let t = Poly.z (List.map (fun (_, i) -> F.of_int i) rk) in

    { v; w; y }, t

  let eval (sol : (Var.t * int) list) (vwy, target : t) =
    let eval' (vps : (Var.t * Poly.polynomial) list) =
      Poly.sum @@
      List.map (fun (k,p) ->
          let a = sol #! k in
          Poly.mul_scalar (F.of_int a) p) vps
    in
    let v = eval' vwy.v in
    let w = eval' vwy.w in
    let y = eval' vwy.y in
    let p = Poly.Infix.(v * w - y) in
    let h, rem = Poly.Infix.(p /% target) in
    assert (Poly.is_zero rem);
    p, h

  [@@@ocaml.warning "-26-27"]
  let test () =
    let open Expr in
    let open Expr.Infix in
    let open Format in
    let x = Var.of_string "i" in
    let e =
      let x = Expr.Term (Var x) in
      x * x + x * Expr.int 2 + Expr.int 3
    in
    ef "----------------@.";
    ef "Expr: %a@." Expr.pp e;
    let gates = Gate.of_expr e in
    ef "Gates: @[<v>%a@]@." Gate.pp_gates gates;
    let vwy, t = build gates in
    let sol = Result.get_ok @@ Gate.eval [x, 3; Gate.one, 1] gates in
    List.iter (fun (v,i) -> ef "%a = %d@." Var.pp v i) sol;
    let p, _h = eval sol (vwy, t) in
    ef "p = %a@." Poly.pp p;
    let h, rem = Poly.Infix.(p /% t) in
    ef "t = %a@." Poly.pp t;
    ef "h = %a@." Poly.pp h;
    ef "rem = %a@." Poly.pp rem

end

module type G = sig
  type t
  type fr

  val one : t

  val ( ~- ) : t -> t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> fr -> t
  val sum : t list -> t

  val ( = ) : t -> t -> bool

  val of_Fr : fr -> t
end

module type CURVE = sig
  module Fr : sig
    include Field.S

    val ( ** ) : t -> Z.t -> t

    val gen : Random.State.t -> t
  end

  module G1 : G with type fr := Fr.t

  module G2 : G with type fr := Fr.t

  module GT : G with type fr := Fr.t

  module Pairing : sig
    val pairing : G1.t -> G2.t -> GT.t
  end
end

module KeyGen(C : CURVE) = struct
  open C

  module Poly = Polynomial.Make(Fr)

  type ek =
    { v_ks (* \{ g^{v_k(s)} \}_{k\inI_{mid}} *) : (Var.t * G1.t) list;
      w_ks (* \{ g^{w_k(s)} \}_{k\in[m]} *) : (Var.t * G1.t) list;
      w_ks_g2 (* \{ g^{w_k(s)} \}_{k\in[m]} *) : (Var.t * G2.t) list;
      y_ks (* \{ g^{y_k(s)} \}_{k\in[m]} *) : (Var.t * G1.t) list;
      av_ks (* \{ g^{\alpha v_k(s)} \}_{k\inI_{mid}} *) : (Var.t * G1.t) list;
      aw_ks (* \{ g^{\alpha w_k(s)} \}_{k\in[m]} *) : (Var.t * G1.t) list;
      ay_ks (* \{ g^{\alpha y_k(s)} \}_{k\in[m]} *) : (Var.t * G1.t) list;
      b_vv_ks (* \{ g^{\beta_v v_k(s)} \}_{k\inI_{mid}} *) : (Var.t * G1.t) list;
      b_ww_ks (* \{ g^{\beta_w w_k(s)} \}_{k\in[m]} *) : (Var.t * G1.t) list;
      b_yy_ks (* \{ g^{\beta_y y_k(s)} \}_{k\in[m]} *) : (Var.t * G1.t) list;
      s'i (* \{ g^s^i \}_{i\in[d]} *) : (int * G1.t) list;
      as'i (* \{ g^{\alpha s^i} \}_{i \in [d]} *) : (int * G1.t) list
     }

  type vk =
    { one (* g^1 *) : G2.t;
      a (* g^\alpha *) : G2.t;
      g (* g^\gamma *) : G2.t;
      b_vg (* g^{b_v\gamma} *) : G2.t;
      b_wg (* g^{b_w\gamma} *) : G2.t;
      b_yg (* g^{b_y\gamma} *) : G2.t;
      ts (* g^{t(s)} *) : G2.t;
      v_ks (* \{ g^{v_k(s)} \}_{k\in [N]} *) : (Var.t * G1.t) list
    }

  let generate rng ~ios ~imid ~vars ({v; w; y}, t) =
    let m (* [m] *) = vars in
    let n (* [N] *) = ios in
    let d = Poly.degree t in

    let random () = Fr.gen rng in
    let s = random () in
    let a (* \alpha *) = random () in
    let b_v (* \beta_v *) = random () in
    let b_w (* \beta_w *) = random () in
    let b_y (* \beta_y *) = random () in
    let gamma (* \gamma *) = random () in

    let ek =
      let v_ks (* \{ g^{v_k(s)} \}_{k\inI_{mid}} *) =
        List.map (fun k ->
            let v_k (* v_k *) = v #! k in
            let v_ks (* v_k(s) *) = Poly.apply v_k s in
            k, G1.of_Fr v_ks) imid
      in
      let w_ks (* \{ g^{w_k(s)} \}_{k\in[m]} *) =
        List.map (fun k ->
            let w_k (* w_k *) = w #! k in
            let w_ks (* w_k(s) *) = Poly.apply w_k s in
            k, G1.of_Fr w_ks) m
      in
      let w_ks_g2 (* \{ g^{w_k(s)} \}_{k\in[m]} *) =
        List.map (fun k ->
            let w_k (* w_k *) = w #! k in
            let w_ks (* w_k(s) *) = Poly.apply w_k s in
            k, G2.of_Fr w_ks) m
      in
      let y_ks (* \{ g^{y_k(s)} \}_{k\in[m]} *) =
        List.map (fun k ->
            let y_k (* y_k *) = y #! k in
            let y_ks (* y_k(s) *) = Poly.apply y_k s in
            k, G1.of_Fr y_ks) m
      in

      let av_ks (* \{ g^{\alpha v_k(s)} \}_{k\inI_{mid}} *) =
        List.map (fun k ->
            let v_k (* v_k *) = v #! k in
            let v_ks (* v_k(s) *) = Poly.apply v_k s in
            let av_ks (* \alpha v_k(s) *) = Fr.(a * v_ks) in
            k, G1.of_Fr av_ks) imid
      in
      let aw_ks (* \{ g^{\alpha w_k(s)} \}_{k\in[m]} *) =
        List.map (fun k ->
            let w_k (* w_k *) = w #! k in
            let w_ks (* w_k(s) *) = Poly.apply w_k s in
            let aw_ks (* \alpha w_k(s) *) = Fr.(a * w_ks) in
            k, G1.of_Fr aw_ks) m
      in
      let ay_ks (* \{ g^{\alpha y_k(s)} \}_{k\in[m]} *) =
        List.map (fun k ->
            let y_k (* y_k *) = y #! k in
            let y_ks (* y_k(s) *) = Poly.apply y_k s in
            let ay_ks (* \alpha y_k(s) *) = Fr.(a * y_ks) in
            k, G1.of_Fr ay_ks) m
      in

      let b_vv_ks (* \{ g^{\beta_v v_k(s)} \}_{k\inI_{mid}} *) =
        List.map (fun k ->
            let v_k (* v_k *) = v #! k in
            let v_ks (* v_k(s) *) = Poly.apply v_k s in
            let b_vv_ks (* \beta_v v_k(s) *) = Fr.(b_v * v_ks) in
            k, G1.of_Fr b_vv_ks) imid
      in
      let b_ww_ks (* \{ g^{\beta_w w_k(s)} \}_{k\in[m]} *) =
        List.map (fun k ->
            let w_k (* w_k *) = w #! k in
            let w_ks (* w_k(s) *) = Poly.apply w_k s in
            let b_ww_ks (* \beta_w w_k(s) *) = Fr.(b_w * w_ks) in
            k, G1.of_Fr b_ww_ks) m
      in
      let b_yy_ks (* \{ g^{\beta_y y_k(s)} \}_{k\in[m]} *) =
        List.map (fun k ->
            let y_k (* y_k *) = y #! k in
            let y_ks (* y_k(s) *) = Poly.apply y_k s in
            let b_yy_ks (* \beta_y y_k(s) *) = Fr.(b_y * y_ks) in
            k, G1.of_Fr b_yy_ks) m
      in

      let s'i (* \{ g^s^i \}_{i\in[d]} *) =
        List.init (d+1) (fun i ->
            let s'i (* s^i *) = Fr.(s ** Z.of_int i) in
            i, G1.of_Fr s'i (* g^s^i *))
      in

      let as'i (* \{ g^{\alpha s^i} \}_{i \in [d]} *) =
        List.init (d+1) (fun i ->
            let s'i (* s^i *) = Fr.(s ** Z.of_int i) in
            let as'i (* \alpha s^i *) = Fr.(a * s'i) in
            i, G1.of_Fr as'i (* g^s^i *))
      in

      { v_ks;
        w_ks;
        w_ks_g2;
        y_ks;
        av_ks;
        aw_ks;
        ay_ks;
        b_vv_ks;
        b_ww_ks;
        b_yy_ks;
        s'i;
        as'i
      }
    in

    let vk =
      let one (* g^1 *) = G2.one in
      let a (* g^\alpha *) = G2.of_Fr a in
      let g (* g^\gamma *) = G2.of_Fr gamma in
      let b_vg (* g^{b_v\gamma} *) = G2.of_Fr Fr.(b_v * gamma) in
      let b_wg (* g^{b_w\gamma} *) = G2.of_Fr Fr.(b_w * gamma) in
      let b_yg (* g^{b_y\gamma} *) = G2.of_Fr Fr.(b_y * gamma) in
      let ts (* g^{t(s)} *) = G2.of_Fr (Poly.apply t s) in
      let v_ks (* \{ g^{v_k(s)} \}_{k\in [N]} *) =
        List.map (fun k ->
            let vk = v #! k in
            let vks = Poly.apply vk s in
            k, G1.of_Fr vks) n
      in
      (* g^{v_0(s)}, g^{w_0(s)}, g^{y_0(s)} are bound in v_ks already
         with key ~one *)
      { one;
        a;
        g;
        b_vg;
        b_wg;
        b_yg;
        ts;
        v_ks }
    in

    ek, vk

end

module Compute(C : CURVE) = struct
  open C

  module Poly = Polynomial.Make(Fr)

  type ek = KeyGen(C).ek

  type proof =
    { v_mids (* g^{v_{mid}(s)} *) : G1.t;
      ws (* g^{w(s)} *) : G1.t;
      ws_g2 (* g^{w(s)} *) : G2.t;
      ys (* g^{y(s)} *) : G1.t;
      hs (* g^{h(s)} *) : G1.t;
      av_mids (* g^{\alpha v_{mid}(s)} *) : G1.t;
      aws (* g^{\alpha w(s)} *) : G1.t;
      ays (* g^{\alpha y(s)} *) : G1.t;
      ahs (* g^{\alpha h(s)} *) : G1.t;
      b_vvsb_wwsb_yys (* g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)} *) : G1.t
    }

  let f (ek : ek) ~vars ~imid (sol : (Var.t * int) list) (h : Poly.t) =
    let m = vars in
    let
      { v_ks;
        w_ks;
        w_ks_g2;
        y_ks;
        av_ks;
        aw_ks;
        ay_ks;
        b_vv_ks;
        b_ww_ks;
        b_yy_ks;
        s'i;
        as'i;
      } : ek = ek
    in
    let c = sol in
    let v_mids (* g^{v_{mid}(s)} *) =
      (* v_mid(x) = \sigma_{k\in I_{mid}} c_k \cdot v_k(x)

         g^{v_{mid}(s) = g^{\sigma_{k\in I_{mid}} c_k \cdot v_k(s)}
                       = g^{c_k_i \cdot v_k_i(s)} + .. + g^{c_k_j \cdot v_k_j(s)}
                       = g^{v_k_i(s)} * c_k_i + .. + g^{v_k_j(s)} * c_k_j
                       = \sigma_{k\in I_{mid}} ( g^{v_k(s)} * c_k )
      *)
      let open G1 in
      sum @@
      List.map (fun k ->
          let v_ks (* g^{v_k(s)} *) = v_ks #! k in
          let c_k (* c_k *) = c #! k in
          v_ks * Fr.of_int c_k
        ) imid
    in
    let ws (* g^{w(s)} *) =
      (* w(x) = \sigma_{k\in [m]} c_k \cdot w_k(x)

         g^{w(s)} = \sigma_{k\in [m]} ( g^{w_k(s)} * c_k )
      *)
      let open G1 in
      sum @@
      List.map (fun k ->
          let w_ks (* g^{w_k(s)} *) = w_ks #! k in
          let c_k (* c_k *) = c #! k in
          w_ks * Fr.of_int c_k
        ) m
    in
    let ws_g2 (* g^{w(s)} *) =
      (* w(x) = \sigma_{k\in [m]} c_k \cdot w_k(x)

         g^{w(s)} = \sigma_{k\in [m]} ( g^{w_k(s)} * c_k )
      *)
      let open G2 in
      sum @@
      List.map (fun k ->
          let w_ks (* g^{w_k(s)} *) = w_ks_g2 #! k in
          let c_k (* c_k *) = c #! k in
          w_ks * Fr.of_int c_k
        ) m
    in
    let ys (* g^{y(s)} *) =
      (* y(x) = \sigma_{k\in [m]} c_k \cdot y_k(x)

         g^{y(s)} = \sigma_{k\in [m]} ( g^{y_k(s)} * c_k )
      *)
      let open G1 in
      sum @@
      List.map (fun k ->
          let y_ks (* g^{y_k(s)} *) = y_ks #! k in
          let c_k (* c_k *) = c #! k in
          y_ks * Fr.of_int c_k
        ) m
    in
    let hs (* g^{h(s)} *) =
      (* h(s) = a0 + a1 * s + a2 * s^2 + .. + ad * s^d
         g^{h(s)} = g^{a0 + a1 * s + a2 * s^2 + .. + ad * s^d}
                  = g^a0 + g^{s * a1} + g^{s^2 * a2} + .. + g^{s^d * ad}
      *)
      let open G1 in
      sum @@
      List.mapi (fun i ai ->
          let s'i = List.assoc i s'i in
          s'i * ai) h
    in
    let av_mids (* g^{\alpha v_{mid}(s)} *) =
      (* g^{\alpha v_{mid}(s) = g^{\sigma_{k\in I_{mid}} c_k \alpha v_k(s)}
                       = \sigma_{k\in I_{mid}} ( g^{\alpha v_k(s)} * \alpha c_k )
      *)
      let open G1 in
      sum @@
      List.map (fun k ->
          let av_ks (* g^{\alpha v_k(s)} *) = av_ks #! k in
          let c_k (* c_k *) = c #! k in
          av_ks * Fr.of_int c_k
        ) imid
    in
    let aws (* g^{\alpha w(s)} *) =
      (* w(x) = \sigma_{k\in [m]} c_k \cdot w_k(x)

         g^{\alpha w(s)} = \sigma_{k\in [m]} ( g^{\alpha w_k(s)} * c_k )
      *)
      let open G1 in
      sum @@
      List.map (fun k ->
          let aw_ks (* g^{\alpha w_k(s)} *) = aw_ks #! k in
          let c_k (* c_k *) = c #! k in
          aw_ks * Fr.of_int c_k
        ) m
    in
    let ays (* g^{\alpha y(s)} *) =
      let open G1 in
      sum @@
      List.map (fun k ->
          let ay_ks (* g^{\alpha y_k(s)} *) = ay_ks #! k in
          let c_k (* c_k *) = c #! k in
          ay_ks * Fr.of_int c_k
        ) m
    in
    let ahs (* g^{\alpha h(s)} *) =
      (* h(s) = a0 + a1 * s + a2 * s^2 + .. + ad * s^d
         g^{\alpha h(s)} = g^{\alpha (a0 + a1 * s + a2 * s^2 + .. + ad * s^d)}
                  = g^a0 *+ g^{\alpha s} * a1 + g^{\alpha s^2} * a2 + .. + g^{\alpha s^d} * ad
      *)
      let open G1 in
      sum @@
      List.mapi (fun i ai ->
          let as'i = List.assoc i as'i in
          as'i * ai) h
    in

    (* Bug of the paper?

       ???

       g^{\beta_v v(s)}  is not computable since   g^{\beta_v v_k(s)} in ek are
       only available for k \in Imid.

       Here instead we use g^{\beta_vmid(s)}
    *)
    let b_vvsb_wwsb_yys (* g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)} *) =
      (* g^{\beta_v v(s) + \beta_w w(s) + \beta_y y(s)}
         = g^{\beta_v v(s)} + g^{\beta_w w(s)} + g^{\beta_y y(s)}
      *)
      let open G1 in
      sum
        @@ List.concat @@
        [ List.map (fun k ->
              let b_vv_ks (* g^{\beta_v v_k(s)} *) = b_vv_ks #! k in
              let c_k (* c_k *) = c #! k in
              b_vv_ks * Fr.of_int c_k) imid;
          List.map (fun k ->
              let b_ww_ks (* g^{\beta_w w_k(s)} *) = b_ww_ks #! k in
              let c_k (* c_k *) = c #! k in
              b_ww_ks * Fr.of_int c_k) m;
          List.map (fun k ->
              let b_yy_ks (* g^{\beta_y y_k(s)} *) = b_yy_ks #! k in
              let c_k (* c_k *) = c #! k in
              b_yy_ks * Fr.of_int c_k) m ]
    in
    { v_mids;
      ws;
      ws_g2;
      ys;
      hs;
      av_mids;
      aws;
      ays;
      ahs;
      b_vvsb_wwsb_yys;
    }

end

module Verify(C : CURVE) = struct
  open C

  type vk = KeyGen(C).vk
  type proof = Compute(C).proof

  let f (vk : vk) ios (proof : proof) =
    (* check that the α and β proof terms are
       correct (e.g., check that e( g^{v_{mid}(s)}, g^α ) = e( g^{α v_{mid}(s)}, g ).
       This requires 8 pairings for the α terms,
       and 3 for the β terms. *)

    (* e(g^{v_{mid}(s)}, g^\alpha) = e(g^{\alpha v_{mid}(s)}, g)
       e(g^{w(s)}, g^\alpha) = e(g^{\alpha w(s)}, g)
       e(g^{y(s)}, g^\alpha) = e(g^{\alpha y(s)}, g)
       e(g^{h(s)}, g^\alpha) = e(g^{\alpha h(s)}, g)

       e(g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)}, g^\gamma)
       = e(g^{\beta_v v(s)}, g^\gamma)  <------- vmid(s) instead?
         + e(g^{\beta_w w(s)}, g^\gamma)
         + e(g^{\beta_y y(s)}, g^\gamma)
       = e(g^{v(s)}, g^{\beta_v \gamma})     <-------- vmid(s) instead?
         + e(g^{w(s)}, g^{\beta_w \gamma})
         + e(g^{y(s)}, g^{\beta_y \gamma})
    *)
    let e = Pairing.pairing in
    let open GT in
    assert (
        e proof.v_mids vk.a
        = e proof.av_mids vk.one
      );

    assert (
        e proof.ws vk.a
        = e proof.aws vk.one
      );

    assert (
        e proof.ys vk.a
        = e proof.ays vk.one
      );

    assert (
        e proof.hs vk.a
        = e proof.ahs vk.one
      );

    assert (
        e proof.b_vvsb_wwsb_yys vk.g

        = e proof.v_mids vk.b_vg
          + e proof.ws vk.b_wg
          + e proof.ys vk.b_yg
      );

    let c = ios in (* should be equal to [N] *)

    let v_ios (* g^{v_{io}(s) *) =
      (* \Pi_{k\in [N]} (g^{v_k(s)})^c_k

         (g^{v_k(s)})^c_k = g^{v_k(s) * c_k}
      *)
      let open G1 in
      sum @@
      List.map (fun (k, c_k) ->
          let v_ks = vk.v_ks #! k in
          v_ks * Fr.of_int c_k
        ) c
    in
    (*A final check (with 3 pairings) verifies the divisibility requirement, i.e.,
      that $e(g^v_0(s) · g^v_{io} · g^v(s),
              g^w_0(s) · g^{w(s))
            / e (g^{y_0(s)} · g^{y(s)}, g)
            = e (g^{h(s), g^{t(s)}) $
    *)
    (* Paper bug? Here again g^v(s) should be g^v_{mid}(s) *)
    (* Our implementation has no v_0 w_0 y_0 *)
    assert (
        e G1.(v_ios + proof.v_mids) proof.ws_g2
        - e proof.ys vk.one

        = e proof.hs vk.ts
      )
end

let protocol_test () =
  prerr_endline "PROTOCOL TEST";
  let module C = Ecp.Bls12_381 in
  let module QAP = QAP(C.Fr) in
  let x = Var.of_string "i" in
  let e =
    let open Expr in
    let open Expr.Infix in
    let x = Expr.Term (Var x) in
    x * x + x * Expr.int 2 + Expr.int 3
  in
  let gates = Gate.of_expr e in
  let vwy, target = QAP.build gates in
  let sol = Result.get_ok @@ Gate.eval [x, 3; Gate.one, 1] gates in
  let _p, h = QAP.eval sol (vwy, target) in
  let rng = Random.State.make_self_init () in
  let ios = Gate.ios gates in
  Format.(ef "ios: @[%a@]@." (list "@ " Var.pp) ios);
  let mids = Gate.mids gates in
  let vars = Var.Set.elements @@ Gate.vars gates in
  let module KeyGen = KeyGen(C) in
  let module Compute = Compute(C) in
  let module Verify = Verify(C) in
  let ek, vk =
    KeyGen.generate rng ~ios ~imid:mids ~vars (vwy, target)
  in
  let proof = Compute.f ek ~vars ~imid:mids sol h in

  let input = [x, 3; Gate.one, 1] in
  let output = [Gate.out, 18] in
  assert (Var.Set.equal (Var.Set.of_list ios) (Var.Set.of_list [x; Gate.one; Gate.out]));
  Verify.f vk (input @ output) proof;
  prerr_endline "PROTOCOL TEST done!"

let test () =
  let module QAP = QAP(Q) in
  QAP.test ();
  protocol_test ()
