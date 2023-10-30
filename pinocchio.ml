open Utils

type 'a vwy = { v : 'a; w : 'a; y : 'a }

let (#!) l k =
  match Var.Map.find_opt k l with
  | Some res -> res
  | None ->
      Format.ef "Variable %a not found@." Var.pp k;
      assert false

module type CURVE = sig
  module Fr : sig
    include Field.S

    val ( ** ) : t -> Z.t -> t

    val gen : Random.State.t -> t
  end

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
  end

  module G1 : G

  module G2 : G

  module GT : G

  module Pairing : sig
    val pairing : G1.t -> G2.t -> GT.t
  end
end


module QAP(F : Field.S) : sig

  type t =
    { vwy : F.t Polynomial.t Var.Map.t vwy;
      target : F.t Polynomial.t }

  val build : Circuit.Gate.t Var.Map.t -> t
  (** compute V, W, Y and a target polynomial t *)

  val eval : (Var.t * int) list -> t -> F.t Polynomial.t * F.t Polynomial.t
  (** compute $p$ and $h$ *)

  val test : unit -> unit

end = struct

  module Poly = Polynomial.Make(F)

  type t =
    { vwy : F.t Polynomial.t Var.Map.t vwy;
      target : F.t Polynomial.t }

  let build (gates : Circuit.Gate.t Var.Map.t) =
    let rk = List.mapi (fun i (v, _) -> v,i) @@ Var.Map.bindings gates in
    let vars = Circuit.vars gates in

    let make_matrix f =
      Var.Map.of_set vars @@ fun k -> Var.Map.mapi (f k) gates
    in

    let v =
      (* $v_k(r_g) = 1$ when gate $g$ has $c_k$ at the left of op *)
      make_matrix @@ fun k _g (l, _r) ->
      match List.assoc_opt k l with
      | None | Some 0 -> 0
      | Some n -> n
    in

    let w =
      (* $w_k(r_g) = 1$ when gate $g$ has $c_k$ at the right of op *)
      make_matrix @@ fun k _g (_l, r) ->
      match List.assoc_opt k r with
      | None | Some 0 -> 0
      | Some n -> n
    in

    let y =
      (* $y_k(r_g) = 1$ when gate (v, _, _) , $v = c_k$ *)
      make_matrix @@ fun k g (_l, _r) ->
      if k = g then 1 else 0
    in

    Var.Map.iter (fun k gns ->
        Var.Map.iter (fun g n ->
            Format.ef "v_%a(r_%a) = %d # gate %a has %a in the left arg@."
              Var.pp k
              Var.pp g
              n
              Var.pp g
              Var.pp k) gns) v;
    Var.Map.iter (fun k gns ->
        Var.Map.iter (fun g n ->
            Format.ef "w_%a(r_%a) = %d # gate %a has %a in the right arg@."
              Var.pp k
              Var.pp g
              n
              Var.pp g
              Var.pp k) gns) w;
    Var.Map.iter (fun k gns ->
        Var.Map.iter (fun g n ->
            Format.ef "y_%a(r_%a) = %d # gate %a outputs %a@."
              Var.pp k
              Var.pp g
              n
              Var.pp g
              Var.pp k) gns) y;

    let make_polynomials u =
      Var.Map.of_set vars @@ fun k ->
      let uk = u #! k in
      Poly.interpolate
        (List.map (fun (g, rg) ->
             let ukrg (* $u_k(r_g)$ *) = uk #! g in
             F.of_int rg, F.of_int ukrg) rk)
    in

    let v = make_polynomials v in
    let w = make_polynomials w in
    let y = make_polynomials y in

    let t = Poly.z (List.map (fun (_, i) -> F.of_int i) rk) in

    { vwy = { v; w; y }; target = t }

  let eval (sol : (Var.t * int) list) { vwy;  target } =
    let eval' (vps : Poly.t Var.Map.t) =
      Poly.sum
      @@ List.of_seq
      @@ Seq.map (fun (k, p) ->
          let a = List.assoc k sol in
          Poly.mul_scalar (F.of_int a) p)
      @@ Var.Map.to_seq vps
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
    let circuit = Circuit.of_expr e in
    ef "Gates: @[<v>%a@]@." Circuit.pp circuit;
    let { vwy; target= t } as qap = build circuit.gates in
    let sol = Result.get_ok @@ Circuit.eval [x, 3; Circuit.one, 1] circuit.gates in
    List.iter (fun (v,i) -> ef "%a = %d@." Var.pp v i) sol;
    let p, _h = eval sol qap in
    ef "p = %a@." Poly.pp p;
    let h, rem = Poly.Infix.(p /% t) in
    ef "t = %a@." Poly.pp t;
    ef "h = %a@." Poly.pp h;
    ef "rem = %a@." Poly.pp rem

end

module Make(C : CURVE) = struct

  include C

  let g1 = (module G1 : G with type t = G1.t)
  let g2 = (module G2 : G with type t = G2.t)

  module Poly = Polynomial.Make(Fr)

  module QAP = QAP(C.Fr)

  (* $ \Sigma_{k\in Dom(m)} f(k,m_k) $ *)
  let sum_map (type t) (module G : G with type t = t) m f =
    let open G in
    Var.Map.fold (fun k v acc -> f k v + acc) m zero

  (* $ \Sigma_{k\in Dom(m)} m_k \cdot c_k$ *)
  let dot (type t) (module G : G with type t = t) m c =
    sum_map (module G) m (fun k mk ->
        let open G in
        let ck = c #! k in
        mk * ck)

  (* $\{ g^s^i \}_{i\in[d]}$ *)
  let powers (type t) (module G : G with type t = t) d s =
    List.init (d+1) (fun i ->
        let s'i = Fr.(s ** Z.of_int i) in
        i, G.of_Fr s'i)

  (* $\Sigma_i c_i x^i$ *)
  let apply_powers (type t) (module G : G with type t = t) (cs : Fr.t Polynomial.t)  xis =
    let open G in
    sum @@
    List.mapi (fun i c ->
        let xi = List.assoc i xis in
        xi * c) cs

  let mul_map (type t) (module G : G with type t = t) m a = Var.Map.map (fun g -> G.(g * a)) m

  module KeyGen = struct

    type ekey =
      { v_mid : G1.t Var.Map.t; (* $\{ g^{v_k(s)} \}_{k\in I_{mid}}$ *)
        v_m : G1.t Var.Map.t; (* $\{ g^{v_k(s)} \}_{k\in [m]$ *)
        w : G1.t Var.Map.t; (* $\{ g^{w_k(s)} \}_{k\in [m]}$ *)
        w_g2 : G2.t Var.Map.t; (* $\{ g^{w_k(s)} \}_{k\in [m]}$ *)
        y : G1.t Var.Map.t; (* $\{ g^{y_k(s)} \}_{k\in[m]}$ *)
        av_mid : G1.t Var.Map.t; (* $\{ g^{\alpha v_k(s)} \}_{k\in I_{mid}}$ *)
        av_m : G1.t Var.Map.t; (* $\{ g^{\alpha v_k(s)} \}_{k\in [m]}$ *)
        aw : G1.t Var.Map.t; (* $\{ g^{\alpha w_k(s)} \}_{k\in [m]}$ *)
        aw_g2 : G2.t Var.Map.t; (* $\{ g^{\alpha w_k(s)} \}_{k\in [m]}$ *)
        ay : G1.t Var.Map.t; (* $\{ g^{\alpha y_k(s)} \}_{k\in [m]}$ *)
        bvv_mid : G1.t Var.Map.t; (* $\{ g^{\beta_v v_k(s)} \}_{k\in I_{mid}}$ *)
        bww : G1.t Var.Map.t; (* $\{ g^{\beta_w w_k(s)} \}_{k\in [m]}$ *)
        byy : G1.t Var.Map.t; (* $\{ g^{\beta_y y_k(s)} \}_{k\in [m]}$ *)
        s'i : (int * G1.t) list; (* $\{ g^{s^i} \}_{i\in[d]}$ *)
        s'i_g2 : (int * G2.t) list; (* $\{ g^{s^i} \}_{i\in[d]}$ *)
        as'i : (int * G1.t) list; (* $\{ g^{\alpha s^i} \}_{i \in [d]}$ *)

        (* required for ZK *)
        at : G1.t; (* $g^{\alpha t(s)}$ *)
        at_g2 : G2.t; (* $g^{\alpha t(s)}$ *)
        bvt : G1.t; (* $g^{\beta_v t(s)}$ *)
        bwt : G1.t; (* $g^{\beta_w t(s)}$ *)
        byt : G1.t; (* $g^{\beta_y t(s)}$ *)
       }

    type vkey =
      { one_g1 : G1.t; (* $g^1$ *)
        one_g2 : G2.t; (* $g^1$ *)
        a_g1 : G1.t; (* $g^\alpha$ *)
        a_g2 : G2.t; (* $g^\alpha$ *)
        g : G2.t; (* $g^\gamma$ *)
        bvg : G2.t; (* $g^{b_v\gamma}$ *)
        bwg : G2.t; (* $g^{b_w\gamma}$ *)
        byg : G2.t; (* $g^{b_y\gamma}$ *)
        t : G2.t; (* $g^{t(s)}$ *)
        v : G1.t Var.Map.t; (* $\{ g^{v_k(s)} \}_{k\in [N]}$ *)
      }

    let generate rng (circuit : Circuit.t) QAP.{vwy; target= t} =
      let imid (* $I_{mid}$ *) = circuit.mids in
      let m (* $[m]$ *) = Circuit.vars circuit.gates in
      let n (* $[N]$ *) = Circuit.ios circuit in
      let d = Poly.degree t in

      let s = Fr.gen rng in
      let a (* $\alpha$ *) = Fr.gen rng in
      let bv (* $\beta_v$ *) = Fr.gen rng in
      let bw (* $\beta_w$ *) = Fr.gen rng in
      let by (* $\beta_y$ *) = Fr.gen rng in
      let g (* $\gamma$ *) = Fr.gen rng in

      (* $\{ g^{u_k(s)} \}_{k\in set}$ *)
      let map_apply_s (type t) (module G : G with type t = t) u set =
        Var.Map.of_set set @@ fun k ->
        let uk = u #! k in
        let uks = Poly.apply uk s in
        G.of_Fr uks
      in

      let ek =
        let v_mid (* $\{ g^{v_k(s)} \}_{k\in I_{mid}}$ *) = map_apply_s g1 vwy.v imid in
        (* It seems required for zk *)
        let v_m (* $\{ g^{v_k(s)} \}_{k\in [m]}$ *) = map_apply_s g1 vwy.v m in
        let w (* $\{ g^{w_k(s)} \}_{k\in[m]}$ *) = map_apply_s g1 vwy.w m in
        let w_g2 (* $\{ g^{w_k(s)} \}_{k\in[m]}$ *) = map_apply_s g2 vwy.w m in
        let y (* $\{ g^{y_k(s)} \}_{k\in[m]}$ *) = map_apply_s g1 vwy.y m in

        let av_mid (* $\{ g^{\alpha v_k(s)} \}_{k\in I_{mid}}$ *) = mul_map g1 v_mid a in
        let av_m (* $\{ g^{\alpha v_k(s)} \}_{k\in [m]$ *) = mul_map g1 v_m a in
        let aw (* $\{ g^{\alpha w_k(s)} \}_{k\in[m]}$ *) = mul_map g1 w a in
        let aw_g2 (* $\{ g^{\alpha w_k(s)} \}_{k\in[m]}$ *) = mul_map g2 w_g2 a in
        let ay (* $\{ g^{\alpha y_k(s)} \}_{k\in[m]}$ *) = mul_map g1 y a in

        let bvv_mid (* $\{ g^{\beta_v v_k(s)} \}_{k\in I_{mid}}$ *) = mul_map g1 v_mid bv in
        let bww (* $\{ g^{\beta_w w_k(s)} \}_{k\in[m]}$ *) = mul_map g1 w bw in
        let byy (* $\{ g^{\beta_y y_k(s)} \}_{k\in[m]}$ *) = mul_map g1 y by in

        let s'i (* $\{ g^s^i \}_{i\in[d]}$ *) = powers g1 d s in

        let s'i_g2 (* $\{ g^s^i \}_{i\in[d]}$ *) = powers g2 d s in
        let as'i (* $\{ g^{\alpha s^i} \}_{i \in [d]}$ *) = List.map G1.(fun (i, g) -> i, g * a) s'i in

        let t = Poly.apply t s in
        let at (* $g^{\alpha t(s)}$ *) = G1.of_Fr Fr.(a * t) in
        let at_g2 (* $g^{\alpha t(s)}$ *) = G2.of_Fr Fr.(a * t) in
        let bvt (* $g^{\beta_v t(s)}$ *) = G1.of_Fr Fr.(bv * t) in
        let bwt (* $g^{\beta_w t(s)}$ *) = G1.of_Fr Fr.(bw * t) in
        let byt (* $g^{\beta_y t(s)}$ *) = G1.of_Fr Fr.(by * t) in

        { v_mid;
          v_m;
          w;
          w_g2;
          y;
          av_mid;
          av_m;
          aw;
          aw_g2;
          ay;
          bvv_mid;
          bww;
          byy;
          s'i;
          s'i_g2;
          as'i;
          at;
          at_g2;
          bvt;
          bwt;
          byt;
        }
      in

      let vk =
        let one_g1 (* $g^1$ *) = G1.one in
        let one_g2 (* $g^1$ *) = G2.one in
        let a_g1 (* $g^\alpha$ *) = G1.of_Fr a in
        let a_g2 (* $g^\alpha$ *) = G2.of_Fr a in
        let g (* $g^\gamma$ *) = G2.of_Fr g in
        let bvg (* $g^{b_v\gamma}$ *) = G2.(g * bv) in
        let bwg (* $g^{b_w\gamma}$ *) = G2.(g * bw) in
        let byg (* $g^{b_y\gamma}$ *) = G2.(g * by) in
        let t (* $g^{t(s)}$ *) = G2.of_Fr (Poly.apply t s) in
        let v (* $\{ g^{v_k(s)} \}_{k\in [N]}$ *) = map_apply_s g1 vwy.v n in
        (* $g^{v_0(s)}, g^{w_0(s)}, g^{y_0(s)}$ are bound in $v_ks$ already with key ~one *)
        { one_g1;
          one_g2;
          a_g1;
          a_g2;
          g;
          bvg;
          bwg;
          byg;
          t;
          v }
      in

      ek, vk

  end

  module Compute = struct

    type proof =
      { v_mid : G1.t; (* $g^{v_{mid}(s)}$ *)
        av_mid : G1.t; (* $g^{\alpha v_{mid}(s)}$ *)

        w : G1.t; (* $g^{w(s)}$ *)
        aw : G1.t; (* $g^{\alpha w(s)}$ *)

        w_g2 : G2.t; (* $g^{w(s)}$ *)
        aw_g2 : G2.t; (* $g^{\alpha w(s)}$ *)

        y : G1.t; (* $g^{y(s)}$ *)
        ay : G1.t; (* $g^{\alpha y(s)}$ *)

        h : G1.t; (* $g^{h(s)}$ *)
        ah : G1.t; (* $g^{\alpha h(s)}$ *)

        bvv_mid_bww_byy : G1.t (* $g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)}$ *)
      }

    let f (ekey : KeyGen.ekey) (sol : Fr.t Var.Map.t) (h_poly : Poly.t) =
      let c = sol in
      let v_mid (* $g^{v_{mid}(s)}$ *) =
        (* $v_{mid}(x) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(x)$

           $g^{v_{mid}(s)} = g^{\Sigma_{k\in I_{mid}} c_k \cdot v_k(s)}$
                         $= g^{c_k_i \cdot v_k_i(s)} + .. + g^{c_k_j \cdot v_k_j(s)}$
                         $= g^{v_k_i(s)} \cdot c_k_i + .. + g^{v_k_j(s)} \cdot c_k_j$
                         $= \Sigma_{k\in I_{mid}} ( g^{v_k(s)} * c_k)$
             *)
        dot g1 ekey.v_mid c
      in
      let w (* $g^{w(s)}$ *) =
        (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

           $g^{w(s)} = \Sigma_{k\in [m]} ( g^{w_k(s)} \cdot c_k )$
        *)
        dot g1 ekey.w c
      in
      let w_g2 (* $g^{w(s)}$ *) =
        (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

           $g^{w(s)} = \Sigma_{k\in [m]} ( g^{w_k(s)} \cdot c_k )$
        *)
        dot g2 ekey.w_g2 c
      in
      let y (* $g^{y(s)}$ *) =
        (* $y(x) = \Sigma_{k\in [m]} c_k \cdot y_k(x)$

           $g^{y(s)} = \Sigma_{k\in [m]} ( g^{y_k(s)} \cdot c_k )$
        *)
        dot g1 ekey.y c
      in
      let h (* $g^{h(s)}$ *) =
        (* $h(s) = a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d$
           $g^{h(s)} = g^{a_0 + a_1 * s + a_2 * s^2 + .. + a_d * s^d}$
                     $= g^{a_0} + g^{s * a_1} + g^{s^2 * a_2} + .. + g^{s^d * a_d}$
        *)
        apply_powers g1 h_poly ekey.s'i
      in
      let av_mid (* $g^{\alpha v_{mid}(s)}$ *) =
        (* $g^{\alpha v_{mid}(s)} = g^{\Sigma_{k\in I_{mid}} c_k \alpha v_k(s)}$
                         $= \Sigma_{k\in I_{mid}} ( g^{\alpha v_k(s)}\cdot c_k )$
        *)
        dot g1 ekey.av_mid c
      in
      let aw (* $g^{\alpha w(s)}$ *) =
        (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

           $g^{\alpha w(s)} = \Sigma_{k\in [m]} ( g^{\alpha w_k(s)} \cdot c_k )$
        *)
        dot g1 ekey.aw c
      in
      let aw_g2 (* $g^{\alpha w(s)}$ *) =
        (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

           $g^{\alpha w(s)} = \Sigma_{k\in [m]} ( g^{\alpha w_k(s)} \cdot c_k )$
        *)
        dot g2 ekey.aw_g2 c
      in
      let ay (* $g^{\alpha y(s)}$ *) =
        dot g1 ekey.ay c
      in
      let ah (* $g^{\alpha h(s)}$ *) =
        (* $h(s) = a_0 + a_1 * s + a_2 * s^2 + .. + a_d * s^d$
           $g^{\alpha h(s)} = g^{\alpha (a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d)}$
                    $= g^1 \cdot a_0 + g^{\alpha s} \cdot a_1 + g^{\alpha s^2} \cdot a_2 + .. + g^{\alpha s^d} \cdot a_d$
        *)
        apply_powers g1 h_poly ekey.as'i
      in

      (* Bug of the paper?

         $g^{\beta_v v(s)}$  is not computable since $g^{\beta_v v_k(s)}$ in ek is only
         available for $I_{mid}$.

         Here instead we use $g^{\beta_v v_{mid}(s)}$
      *)
      let bvv_mid_bww_byy (* $g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)}$ *) =
        (* $g^{\beta_v v(s) + \beta_w w(s) + \beta_y y(s)}
           = g^{\beta_v v(s)} + g^{\beta_w w(s)} + g^{\beta_y y(s)}$ *)
        let open G1 in
        dot g1 ekey.bvv_mid c
        + dot g1 ekey.bww c
        + dot g1 ekey.byy c
      in
      { v_mid; av_mid;
        w; aw;
        w_g2; aw_g2;
        y; ay;
        h; ah;
        bvv_mid_bww_byy;
      }

  end

  module Verify = struct

    let f (vkey : KeyGen.vkey) (ios : Fr.t Var.Map.t) (proof : Compute.proof) =
      (* check that the α and β proof terms are
         correct (e.g., check that $e( g^{v_{mid}(s)}, g^\alpha ) = e( g^{\alpha v_{mid}(s)}, g )$.
         This requires 8 pairings for the α terms,
         and 3 for the β terms. *)

      (* $e(g^{v_{mid}(s)}, g^\alpha) = e(g^{\alpha v_{mid}(s)}, g)$
         $e(g^{w(s)}, g^\alpha) = e(g^{\alpha w(s)}, g)$
         $e(g^{y(s)}, g^\alpha) = e(g^{\alpha y(s)}, g)$
         $e(g^{h(s)}, g^\alpha) = e(g^{\alpha h(s)}, g)$

         $e(g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)}, g^\gamma)$
         $= e(g^{\beta_v v(s)}, g^\gamma)$  <------- vmid(s) instead?
           $+ e(g^{\beta_w w(s)}, g^\gamma)$
           $+ e(g^{\beta_y y(s)}, g^\gamma)$
         $= e(g^{v(s)}, g^{\beta_v \gamma})$     <-------- vmid(s) instead?
           $+ e(g^{w(s)}, g^{\beta_w \gamma})$
           $+ e(g^{y(s)}, g^{\beta_y \gamma})$
      *)
      let e = Pairing.pairing in
      let open GT in

      (* All the ingredients must be KC checked *)

      let kc_check x ax = e x vkey.a_g2 = e ax vkey.one_g2 in
      let kc_check_g2 x ax = e vkey.a_g1 x = e vkey.one_g1 ax in

      (* KC check
         $v_{mid}(s)$ is really a linear combination of $\{v_k(s)\}$.
         Actually, $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$  *)
      assert (kc_check proof.v_mid proof.av_mid);

      (* KC check
         $w(s)$ is really a linear combination of $\{w_k(s)\}$.
         Actually, $w(s) = \Sigma_{k\in [m]} c_k \cdot w_k(s)$ *)
      assert (kc_check proof.w proof.aw);
      assert (kc_check_g2 proof.w_g2 proof.aw_g2);

      (* KC check
         $y(s)$ is really a linear combination of $\{y_k(s)\}$.
         Actually, $y(s) = \Sigma_{k\in [m]} c_k \cdot y_k(s)$ *)
      assert (kc_check proof.y proof.ay);

      (* KC check
         $h(s)$ is really a linear combination of $\{s^i\}$.
         Actually, $h(s) = a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d$

          Protocol 1 requires this but do we really need it?
      *)
      assert (kc_check proof.h proof.ah);

      (* I still do not understand why we need this *)
      (* KC check
         $g^{\beta_vv_{mid}(s)+\beta_ww(s)+\beta_yy(s)}$ is really a linear combination of
         $\{g^{\beta_v v_k(s)}\}$, $\{g^{\beta_v v_k(s)}\}$, and $\{g^{\beta_v v_k(s)}\}$. *)
      assert (
          e proof.bvv_mid_bww_byy vkey.g
          = e proof.v_mid vkey.bvg
            + e proof.w vkey.bwg
            + e proof.y vkey.byg
        );

      let c = ios in (* $Dom(c) = [N]$ *)

      let v_ios (* $g^{v_{io}(s)}$ *) =
        (* $\Pi_{k\in [N]} (g^{v_k(s)})^{c_k}$

           $(g^{v_k(s)})^{c_k} = g^{v_k(s) \cdot c_k}$
        *)
        sum_map g1 c @@ fun k c_k ->
            let v_ks = vkey.v #! k in
            G1.(v_ks * c_k)
      in
      (*A final check (with 3 pairings) verifies the divisibility requirement, i.e.,
        that $e(g^{v_0(s)} \cdot g^{v_{io}} \cdot g^{v_{mid}(s)},~
                g^{w_0(s)} \cdot g^{w(s)})
              ~/~ e (g^{y_0(s)} \cdot g^{y(s)},~ g)$
              $= e (g^{h(s)},~ g^{t(s)}) $
      *)
      (* Paper bug. Here again $g^v(s)$ is mistakenly used instead of $g^{v_{mid}(s)}$.
         $g^{v_{io}} \cdot g^{v(s)}$ double-counts the IO vars. *)
      (* In our implementation, $v_0(s), w_0(s), y_0(s)$ are in $v_{io}(s)$ *)
      (* Here is to prove $p(s) = h(s) \cdot t(s)$.

         LHS:
         $e(g^{v_0(s)} \cdot g^{v_{io}} \cdot g^{v_{mid}(s)},~ g^{w_0(s)} \cdot g^{w(s)})
              ~/~ e(g^{y_0(s)} \cdot g^{y(s)}, g^1)$
                $= e(g^{v_0(s)} \cdot g^{v(s)},~g^{w_0(s)} \cdot g^{w(s)})
                       ~/~ e(g^{y_0(s)} \cdot g^{y(s)}, g^1)$
                $= e(g^{(v_0(s) + v(s)) \cdot (w_0(s) + w(s))}, g^1)
                      ~/~ e(g^{y_0(s) + y(s)}, g^1)$
                $= e(g^{(v_0(s) + v(s)) \cdot (w_0(s) + w(s))} / g^{y_0(s) + y(s)}, g^1)$
                $= e(g^{(v_0(s) + v(s)) \cdot (w_0(s) + w(s)) - (y_0(s) + y(s))}, g^1)$
                $= e(g^{p(s)}, g^1)$

         RHS:
         $e (g^{h(s)},~ g^{t(s)})$
      *)
      assert (
          e G1.(v_ios + proof.v_mid) proof.w_g2
          - e proof.y vkey.one_g2
          = e proof.h vkey.t
        )
  end

  module ZKCompute = struct

    type proof = Compute.proof =
      { v_mid : G1.t; (* $g^{v_{mid}(s)}$ *)
        av_mid : G1.t; (* $g^{\alpha v_{mid}(s)}$ *)

        w : G1.t; (* $g^{w(s)}$ *)
        aw : G1.t; (* $g^{\alpha w(s)}$ *)

        w_g2 : G2.t; (* $g^{w(s)}$ *)
        aw_g2 : G2.t; (* $g^{\alpha w(s)}$ *)

        y : G1.t; (* $g^{y(s)}$ *)
        ay : G1.t; (* $g^{\alpha y(s)}$ *)

        h : G1.t; (* $g^{h(s)}$ *)
        ah : G1.t; (* $g^{\alpha h(s)}$ *)

        bvv_mid_bww_byy : G1.t (* $g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)}$ *)
      }

    let f rng (target : Poly.t) (ekey : KeyGen.ekey) (sol : Fr.t Var.Map.t) (h_poly : Poly.t) =

      let dv (* $\delta_v$ *) = Fr.gen rng in
      let dw (* $\delta_w$ *) = Fr.gen rng in
      let dy (* $\delta_y$ *) = Fr.gen rng in
      let t (* $g^{t(s)}$ *) = apply_powers g1 target ekey.s'i in
      let t_g2 (* $g^{t(s)}$ *) = apply_powers g2 target ekey.s'i_g2 in
      let a (* $g^\alpha$ *) = List.assoc 0 ekey.as'i in
      let c = sol in
      let v_mid (* $g^{v_{mid}(s)}$ *) = dot g1 ekey.v_mid c in
      let v'_mid (* $g^{v_{mid}(s) + \delta_v t(s)}$ *) = G1.(v_mid + t * dv) in
      let v_m (* $g^{v(s)}$ *) = dot g1 ekey.v_m c in
      let w (* $g^{w(s)}$ *) = dot g1 ekey.w c in
      let w' (* $g^{w(s) + \delta_w t(s)}$ *) = G1.(w + t * dw) in

      let w_g2 (* $g^{w(s)}$ *) = dot g2 ekey.w_g2 c in
      let w'_g2 (* $g^{w(s) + \delta_w t(s)}$ *) = G2.(w_g2 + t_g2 * dw) in
      let y (* $g^{y(s)}$ *) = dot g1 ekey.y c in
      let y' (* $g^{y(s) + \delta_y t(s)}$ *) = G1.(y + t * dy) in
      let h (* $g^{h(s)}$ *) = apply_powers g1 h_poly ekey.s'i in

      (* $p'(x) := (\Sigma c_k v_k(x) + \delta_v t(x))
                     \cdot (\Sigma c_k w_k(x) + \delta_w t(x))
                     - (\Sigma c_k y_k(x) + \delta_y t(x))$
             $= (\Sigma c_k v'(x)) \cdot (\Sigma c_k w'(x)) - \Sigma c_k y_k(x)
                  + (\Sigma c_k v_k(x)) \cdot \delta_w t(x)
                  + (\Sigma c_k w_k(x)) \cdot \delta_v t(x)
                  + \delta_v \delta_w (t(x))^2
                  - \delta_y t(x)$
             $= p(x)
                  + (\Sigma c_k v_k(x)) \cdot \delta_w t(x)
                  + (\Sigma c_k w_k(x)) \cdot \delta_v t(x)
                  + \delta_v \delta_w (t(x))^2
                  - \delta_y t(x)$ since $ p(x)$
             $= h(x) \cdot t(x)
                  + (\Sigma c_k v_k(x)) \cdot \delta_w t(x)
                  + (\Sigma c_k w_k(x)) \cdot \delta_v t(x)
                  + \delta_v \delta_w (t(x))^2
                  - \delta_y t(x)$ since $p(x) = h(x) \cdot t(x)$
             $= (h(x) + (\Sigma c_k v_k(x)) \cdot \delta_w
                      + (\Sigma c_k w_k(x)) \cdot \delta_v
                      + \delta_v \delta_w t(x)
                      - \delta_y) \cdot t(x)$

         $h'(x) := h(x) + (\Sigma c_k v_k(x)) \cdot \delta_w
                         + (\Sigma c_k w_k(x)) \cdot \delta_v
                         + \delta_v \delta_w t(x)
                         - \delta_y$

         $p'(x) = h'(x) \cdot t(x)$
      *)
      let h' (* $h'(s) = h(s) + v(s) \cdot \delta_w + w(s) \cdot \delta_v + \delta_v \delta_w t(s) - \delta_y$ *) =
        let open G1 in
        h + v_m * dw + w * dv + t * dv * dw - one * dy
      in
      let av_mid (* $g^{\alpha v_{mid}(s)}$ *) = dot g1 ekey.av_mid c in
      let av'_mid (* $g^{\alpha( v_{mid}(s) + \delta_v t(s))}$ *) = G1.(av_mid + ekey.at * dv) in
      let av_m (* $g^{\alpha v(s)}$ *) = dot g1 ekey.av_m c in
      let aw (* $g^{\alpha w(s)}$ *) = dot g1 ekey.aw c in
      let aw' (* $g^{\alpha (w(s) + \delta_w t(s)}$ *) = G1.(aw + ekey.at * dw) in
      let aw_g2 (* $g^{\alpha w(s)}$ *) = dot g2 ekey.aw_g2 c in
      let aw'_g2 (* $g^{\alpha (w(s) + \delta_w t(s)}$ *) = G2.(aw_g2 + ekey.at_g2 * dw) in
      let ay (* $g^{\alpha y(s)}$ *) = dot g1 ekey.ay c in
      let ay' (* $g^{\alpha (y(s) + \delta_y t(s))}$ *) = G1.(ay + ekey.at * dy) in
      let ah (* $g^{\alpha h(s)}$ *) = apply_powers g1 h_poly ekey.as'i in
      let ah' (* $\alpha h'(s) = \alpha h(s) + \alpha v(s) \delta_w + \alpha w(s) \delta_v + \alpha\delta_v\delta_w t(s) - \alpha \delta_y$ *) =
        G1.(ah + av_m * dw + aw * dv + ekey.at * Fr.(dv * dw) - a * dy)
      in
      let bvv'_mid_bww'_byy' (* $g^{\beta_vv'(s)+\beta_ww'(s)+\beta_yy'(s)}$ *) =
        (* $g^{\beta_v v(s) + \beta_w w(s) + \beta_y y(s)}
           = g^{\beta_v v(s)} + g^{\beta_w w(s)} + g^{\beta_y y(s)}$ *)
        let open G1 in
        let bvv_mid = dot g1 ekey.bvv_mid c in
        let bvv'_mid (* $\beta_v v'(s) = \beta_v v(s) + \beta_v \delta_v t(s)$ *) = bvv_mid + ekey.bvt * dv in
        let bww = dot g1 ekey.bww c in
        let bww' (* $\beta_w w'(s) = \beta_w w(s) + \beta_w \delta_w t(s)$ *) = bww + ekey.bwt * dw in
        let byy = dot g1 ekey.byy c in
        let byy' (* $\beta_y y'(s) = \beta_y y(s) + \beta_y \delta_y t(s)$ *) = byy + ekey.byt * dy in
        bvv'_mid + bww' + byy'
      in
      { v_mid= v'_mid;
        av_mid= av'_mid;
        w= w';
        aw= aw';
        w_g2= w'_g2;
        aw_g2 = aw'_g2;
        y = y';
        ay = ay';
        h = h';
        ah = ah';
        bvv_mid_bww_byy = bvv'_mid_bww'_byy';
      }
  end
end


let protocol_test () =
  prerr_endline "PROTOCOL TEST";
  let module C = Ecp.Bls12_381 in
  let module Impl = Make(C) in
  let open Impl in
  let x = Var.of_string "i" in
  let e =
    let open Expr in
    let open Expr.Infix in
    let x = Expr.Term (Var x) in
    x * x + x * Expr.int 2 + Expr.int 3
  in
  let rng = Random.State.make_self_init () in
  let prepare e =
    let circuit = Circuit.of_expr e in
    let qap = QAP.build circuit.gates in
    circuit, qap
  in
  let circuit, qap = prepare e in
  let ekey, vkey = KeyGen.generate rng circuit qap in
  let proof =
    let sol = Result.get_ok @@ Circuit.eval [x, 3; Circuit.one, 1] circuit.gates in
    let _p, h = QAP.eval sol qap in
    Compute.f ekey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq sol) h
  in
  prerr_endline "VC proof done";
  let () =
    let ios = Circuit.ios circuit in
    assert (Var.Set.equal ios (Var.Set.of_list [x; Circuit.one; Circuit.out]));
    let input = [x, 3; Circuit.one, 1] in
    let output = [Circuit.out, 18] in
    Verify.f vkey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq (input @ output)) proof
  in
  prerr_endline "VC done!";

  let zcircuit = { circuit with mids = Var.Set.add x circuit.mids } in
  let ekey, vkey = KeyGen.generate rng zcircuit qap in
  let zkproof =
    let sol = Result.get_ok @@ Circuit.eval [x, 3; Circuit.one, 1] circuit.gates in
    let _p, h = QAP.eval sol qap in
    (* hide x *)
    ZKCompute.f rng qap.target ekey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq sol) h
  in
  let () =
    let ios = Circuit.ios zcircuit in
    assert (Var.Set.equal ios (Var.Set.of_list [Circuit.one; Circuit.out]));
    let input = [Circuit.one, 1] in
    let output = [Circuit.out, 18] in
    Verify.f vkey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq (input @ output)) zkproof
  in
  prerr_endline "PROTOCOL TEST done!"

let test () =
  let module QAP = QAP(Q) in
  QAP.test ();
  protocol_test ()
