open Utils

module PQ = Polynomial.Make(Q)

type 'a vwy = { v : 'a; w : 'a; y : 'a }

let (#!) l k =
  match Var.Map.find_opt k l with
  | Some res -> res
  | None ->
      Format.ef "Variable %a not found@." Var.pp k;
      assert false

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

  type poly = Poly.t

  type t =
    { vwy : F.t Polynomial.t Var.Map.t vwy;
      target : F.t Polynomial.t }

  let build (gates : Circuit.Gate.t Var.Map.t) =
    let rk = List.mapi (fun i (v, _) -> v,i) @@ Var.Map.bindings gates in
    let vars = Circuit.vars gates in
    let v =
      (* $v_k(r_g) = 1$ when gate $g$ has $c_k$ at the left of op *)
      Var.Map.of_set vars @@ fun k ->
          Var.Map.map (fun (l, _r) ->
              match List.assoc_opt k l with
              | None | Some 0 -> 0
              | Some n -> n) gates
    in

    let w =
      (* $w_k(r_g) = 1$ when gate $g$ has $c_k$ at the right of op *)
      Var.Map.of_set vars @@ fun k ->
          Var.Map.map (fun (_l, r) ->
              match List.assoc_opt k r with
              | None | Some 0 -> 0
              | Some n -> n) gates
    in

    let y =
      (* $y_k(r_g) = 1$ when gate (v, _, _) , $v = c_k$ *)
      Var.Map.of_set vars @@ fun k ->
          Var.Map.mapi (fun g _ ->
              if k = g then 1 else 0) gates
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

    let v =
      Var.Map.of_set vars @@ fun k ->
          let vk = v #! k in
          let p =
            Poly.interpolate
              (List.map (fun (g, rg) ->
                   let vkrg (* $v_k(r_g)$ *) = vk #! g in
                   F.of_int rg, F.of_int vkrg) rk)
          in
          Format.ef "v_%a(x) = %a@." Var.pp k Poly.pp p;
          p
    in

    let w =
      Var.Map.of_set vars @@ fun k ->
          let wk = w #! k in
          let p =
            Poly.interpolate
              (List.map (fun (g, rg) ->
                   let wkrg (* $w_k(r_g)$ *) = wk #! g in
                   F.of_int rg, F.of_int wkrg) rk)
          in
          Format.ef "w_%a(x) = %a@." Var.pp k Poly.pp p;
          p
    in

    let y =
      Var.Map.of_set vars @@ fun k ->
          let yk = y #! k in
          let p =
            Poly.interpolate
              (List.map (fun (g, rg) ->
                   let ykrg (* $y_k(r_g)$ *) = yk #! g in
                   F.of_int rg, F.of_int ykrg) rk)
          in
          Format.ef "y_%a(x) = %a@." Var.pp k Poly.pp p;
          p
    in

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

module type G = sig
  type t
  type fr

  val zero : t

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
  module QAP = QAP(Fr)

  type ekey =
    { v_ks : G1.t Var.Map.t; (* $\{ g^{v_k(s)} \}_{k\in I_{mid}}$ *)
      v_ks_m : G1.t Var.Map.t; (* $\{ g^{v_k(s)} \}_{k\in [m]$ *)
      w_ks : G1.t Var.Map.t; (* $\{ g^{w_k(s)} \}_{k\in [m]}$ *)
      w_ks_g2 : G2.t Var.Map.t; (* $\{ g^{w_k(s)} \}_{k\in [m]}$ *)
      y_ks : G1.t Var.Map.t; (* $\{ g^{y_k(s)} \}_{k\in[m]}$ *)
      av_ks : G1.t Var.Map.t; (* $\{ g^{\alpha v_k(s)} \}_{k\in I_{mid}}$ *)
      aw_ks : G1.t Var.Map.t; (* $\{ g^{\alpha w_k(s)} \}_{k\in [m]}$ *)
      ay_ks : G1.t Var.Map.t; (* $\{ g^{\alpha y_k(s)} \}_{k\in [m]}$ *)
      b_vv_ks : G1.t Var.Map.t; (* $\{ g^{\beta_v v_k(s)} \}_{k\in I_{mid}}$ *)
      b_ww_ks : G1.t Var.Map.t; (* $\{ g^{\beta_w w_k(s)} \}_{k\in [m]}$ *)
      b_yy_ks : G1.t Var.Map.t; (* $\{ g^{\beta_y y_k(s)} \}_{k\in [m]}$ *)
      s'i : (int * G1.t) list; (* $\{ g^{s^i} \}_{i\in[d]}$ *)
      s'i_g2 : (int * G2.t) list; (* $\{ g^{s^i} \}_{i\in[d]}$ *)
      as'i : (int * G1.t) list (* $\{ g^{\alpha s^i} \}_{i \in [d]}$ *)
     }

  type vkey =
    { one : G2.t; (* $g^1$ *)
      a : G2.t; (* $g^\alpha$ *)
      g : G2.t; (* $g^\gamma$ *)
      b_vg : G2.t; (* $g^{b_v\gamma}$ *)
      b_wg : G2.t; (* $g^{b_w\gamma}$ *)
      b_yg : G2.t; (* $g^{b_y\gamma}$ *)
      ts : G2.t; (* $g^{t(s)}$ *)
      v_ks : G1.t Var.Map.t (* $\{ g^{v_k(s)} \}_{k\in [N]}$ *)
    }

  let generate rng (circuit : Circuit.t) QAP.{vwy= {v; w; y}; target= t} =
    let imid (* $I_{mid}$ *) = circuit.mids in
    let m (* $[m]$ *) = Circuit.vars circuit.gates in
    let n (* $[N]$ *) = Circuit.ios circuit in
    let d = Poly.degree t in

    let s = Fr.gen rng in
    let a (* $\alpha$ *) = Fr.gen rng in
    let b_v (* $\beta_v$ *) = Fr.gen rng in
    let b_w (* $\beta_w$ *) = Fr.gen rng in
    let b_y (* $\beta_y$ *) = Fr.gen rng in
    let gamma (* $\gamma$ *) = Fr.gen rng in

    let ek =
      let v_ks (* $\{ g^{v_k(s)} \}_{k\in I_{mid}}$ *) =
        Var.Map.of_set imid @@ fun k ->
            let v_k = v #! k in
            let v_ks = Poly.apply v_k s in
            G1.of_Fr v_ks
      in

      (* It seems required for zk *)
      let v_ks_m (* $\{ g^{v_k(s)} \}_{k\in [m]}$ *) =
        Var.Map.of_set m @@ fun k ->
            let v_k = v #! k in
            let v_ks = Poly.apply v_k s in
            G1.of_Fr v_ks
      in

      let w_ks (* $\{ g^{w_k(s)} \}_{k\in[m]}$ *) =
        Var.Map.of_set m @@ fun k ->
            let w_k = w #! k in
            let w_ks = Poly.apply w_k s in
            G1.of_Fr w_ks
      in
      let w_ks_g2 (* $\{ g^{w_k(s)} \}_{k\in[m]}$ *) =
        Var.Map.of_set m @@ fun k ->
            let w_k = w #! k in
            let w_ks = Poly.apply w_k s in
            G2.of_Fr w_ks
      in
      let y_ks (* \{ g^{y_k(s)} \}_{k\in[m]} *) =
        Var.Map.of_set m @@ fun k ->
            let y_k = y #! k in
            let y_ks = Poly.apply y_k s in
            G1.of_Fr y_ks
      in

      let av_ks (* $\{ g^{\alpha v_k(s)} \}_{k\in I_{mid}}$ *) =
        Var.Map.of_set imid @@ fun k ->
            let v_k = v #! k in
            let v_ks = Poly.apply v_k s in
            let av_ks = Fr.(a * v_ks) in
            G1.of_Fr av_ks
      in
      let aw_ks (* $\{ g^{\alpha w_k(s)} \}_{k\in[m]}$ *) =
        Var.Map.of_set m @@ fun k ->
            let w_k = w #! k in
            let w_ks = Poly.apply w_k s in
            let aw_ks = Fr.(a * w_ks) in
             G1.of_Fr aw_ks
      in
      let ay_ks (* $\{ g^{\alpha y_k(s)} \}_{k\in[m]}$ *) =
        Var.Map.of_set m @@ fun k ->
            let y_k = y #! k in
            let y_ks = Poly.apply y_k s in
            let ay_ks = Fr.(a * y_ks) in
            G1.of_Fr ay_ks
      in

      let b_vv_ks (* $\{ g^{\beta_v v_k(s)} \}_{k\in I_{mid}}$ *) =
        Var.Map.of_set imid @@ fun k ->
            let v_k = v #! k in
            let v_ks = Poly.apply v_k s in
            let b_vv_ks = Fr.(b_v * v_ks) in
            G1.of_Fr b_vv_ks
      in
      let b_ww_ks (* $\{ g^{\beta_w w_k(s)} \}_{k\in[m]}$ *) =
        Var.Map.of_set m @@ fun k ->
            let w_k = w #! k in
            let w_ks = Poly.apply w_k s in
            let b_ww_ks = Fr.(b_w * w_ks) in
            G1.of_Fr b_ww_ks
      in
      let b_yy_ks (* $\{ g^{\beta_y y_k(s)} \}_{k\in[m]}$ *) =
        Var.Map.of_set m @@ fun k ->
            let y_k = y #! k in
            let y_ks = Poly.apply y_k s in
            let b_yy_ks = Fr.(b_y * y_ks) in
            G1.of_Fr b_yy_ks
      in

      let s'i (* $\{ g^s^i \}_{i\in[d]}$ *) =
        List.init (d+1) (fun i ->
            let s'i = Fr.(s ** Z.of_int i) in
            i, G1.of_Fr s'i)
      in

      let s'i_g2 (* $\{ g^s^i \}_{i\in[d]}$ *) =
        List.init (d+1) (fun i ->
            let s'i = Fr.(s ** Z.of_int i) in
            i, G2.of_Fr s'i)
      in

      let as'i (* $\{ g^{\alpha s^i} \}_{i \in [d]}$ *) =
        List.init (d+1) (fun i ->
            let s'i = Fr.(s ** Z.of_int i) in
            let as'i = Fr.(a * s'i) in
            i, G1.of_Fr as'i)
      in

      { v_ks;
        v_ks_m;
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
        s'i_g2;
        as'i
      }
    in

    let vk =
      let one (* $g^1$ *) = G2.one in
      let a (* $g^\alpha$ *) = G2.of_Fr a in
      let g (* $g^\gamma$ *) = G2.of_Fr gamma in
      let b_vg (* $g^{b_v\gamma}$ *) = G2.of_Fr Fr.(b_v * gamma) in
      let b_wg (* $g^{b_w\gamma}$ *) = G2.of_Fr Fr.(b_w * gamma) in
      let b_yg (* $g^{b_y\gamma}$ *) = G2.of_Fr Fr.(b_y * gamma) in
      let ts (* $g^{t(s)}$ *) = G2.of_Fr (Poly.apply t s) in
      let v_ks (* $\{ g^{v_k(s)} \}_{k\in [N]}$ *) =
        Var.Map.of_set n @@ fun k ->
            let vk = v #! k in
            let vks = Poly.apply vk s in
            G1.of_Fr vks
      in
      (* $g^{v_0(s)}, g^{w_0(s)}, g^{y_0(s)}$ are bound in $v_ks$ already with key ~one *)
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

  type ekey = KeyGen(C).ekey

  type proof =
    { v_mids : G1.t; (* $g^{v_{mid}(s)}$ *)
      ws : G1.t; (* $g^{w(s)}$ *)
      ws_g2 : G2.t; (* $g^{w(s)}$ *)
      ys : G1.t; (* $g^{y(s)}$ *)
      hs : G1.t; (* $g^{h(s)}$ *)
      av_mids : G1.t; (* $g^{\alpha v_{mid}(s)}$ *)
      aws : G1.t; (* $g^{\alpha w(s)}$ *)
      ays : G1.t; (* $g^{\alpha y(s)}$ *)
      ahs : G1.t; (* $g^{\alpha h(s)}$ *)
      b_vvsb_wwsb_yys : G1.t (* $g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)}$ *)
    }

  let sum_map_g1 set f =
    (* $ \Sigma_{k\in set} f(k) $ *)
    let open G1 in
    Var.Set.fold (fun v acc -> f v + acc) set zero

  let sum_map_g2 set f =
    (* $ \Sigma_{k\in set} f(k) $ *)
    let open G2 in
    Var.Set.fold (fun v acc -> f v + acc) set zero

  let f (ekey : ekey) (circuit : Circuit.t) (sol : int Var.Map.t) (h : Poly.t) =
    let imid (* $I_{mid}$ *) = circuit.mids in
    let m (* $[m]$ *) = Circuit.vars circuit.gates in
    let
      { v_ks;
        v_ks_m = _;
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
        s'i_g2 = _;
        as'i;
      } : ekey = ekey
    in
    let c = sol in
    let v_mids (* $g^{v_{mid}(s)}$ *) =
      (* $v_{mid}(x) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(x)$

         $g^{v_{mid}(s)} = g^{\Sigma_{k\in I_{mid}} c_k \cdot v_k(s)}$
                       $= g^{c_k_i \cdot v_k_i(s)} + .. + g^{c_k_j \cdot v_k_j(s)}$
                       $= g^{v_k_i(s)} \cdot c_k_i + .. + g^{v_k_j(s)} \cdot c_k_j$
                       $= \Sigma_{k\in I_{mid}} ( g^{v_k(s)} * c_k)$
           *)
      let open G1 in
      sum_map_g1 imid @@ fun k ->
          let v_ks = v_ks #! k in
          let c_k = c #! k in
          v_ks * Fr.of_int c_k
    in
    let ws (* $g^{w(s)}$ *) =
      (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

         $g^{w(s)} = \Sigma_{k\in [m]} ( g^{w_k(s)} \cdot c_k )$
      *)
      let open G1 in
      sum_map_g1 m @@ fun k ->
          let w_ks = w_ks #! k in
          let c_k = c #! k in
          w_ks * Fr.of_int c_k
    in
    let ws_g2 (* $g^{w(s)}$ *) =
      (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

         $g^{w(s)} = \Sigma_{k\in [m]} ( g^{w_k(s)} \cdot c_k )$
      *)
      let open G2 in
      sum_map_g2 m @@ fun k ->
          let w_ks = w_ks_g2 #! k in
          let c_k = c #! k in
          w_ks * Fr.of_int c_k
    in
    let ys (* $g^{y(s)}$ *) =
      (* $y(x) = \Sigma_{k\in [m]} c_k \cdot y_k(x)$

         $g^{y(s)} = \Sigma_{k\in [m]} ( g^{y_k(s)} \cdot c_k )$
      *)
      let open G1 in
      sum_map_g1 m @@ fun k ->
          let y_ks = y_ks #! k in
          let c_k = c #! k in
          y_ks * Fr.of_int c_k
    in
    let hs (* $g^{h(s)}$ *) =
      (* $h(s) = a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d$
         $g^{h(s)} = g^{a_0 + a_1 * s + a_2 * s^2 + .. + a_d * s^d}$
                   $= g^{a_0} + g^{s * a_1} + g^{s^2 * a_2} + .. + g^{s^d * a_d}$
      *)
      let open G1 in
      sum @@
      List.mapi (fun i ai ->
          let s'i = List.assoc i s'i in
          s'i * ai) h
    in
    let av_mids (* $g^{\alpha v_{mid}(s)}$ *) =
      (* $g^{\alpha v_{mid}(s)} = g^{\Sigma_{k\in I_{mid}} c_k \alpha v_k(s)}$
                       $= \Sigma_{k\in I_{mid}} ( g^{\alpha v_k(s)}\cdot c_k )$
      *)
      let open G1 in
      sum_map_g1 imid @@ fun k ->
          let av_ks = av_ks #! k in
          let c_k = c #! k in
          av_ks * Fr.of_int c_k
    in
    let aws (* $g^{\alpha w(s)}$ *) =
      (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

         $g^{\alpha w(s)} = \Sigma_{k\in [m]} ( g^{\alpha w_k(s)} \cdot c_k )$
      *)
      let open G1 in
      sum_map_g1 m @@ fun k ->
          let aw_ks = aw_ks #! k in
          let c_k = c #! k in
          aw_ks * Fr.of_int c_k
    in
    let ays (* $g^{\alpha y(s)}$ *) =
      let open G1 in
      sum_map_g1 m @@ fun k ->
          let ay_ks = ay_ks #! k in
          let c_k = c #! k in
          ay_ks * Fr.of_int c_k
    in
    let ahs (* $g^{\alpha h(s)}$ *) =
      (* $h(s) = a_0 + a_1 * s + a_2 * s^2 + .. + a_d * s^d$
         $g^{\alpha h(s)} = g^{\alpha (a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d)}$
                  $= g^1 \cdot a_0 + g^{\alpha s} \cdot a_1 + g^{\alpha s^2} * a_2 + .. + g^{\alpha s^d} \cdot a_d$
      *)
      let open G1 in
      sum @@
      List.mapi (fun i ai ->
          let as'i = List.assoc i as'i in
          as'i * ai) h
    in

    (* Bug of the paper?

       $g^{\beta_v v(s)}$  is not computable since $g^{\beta_v v_k(s)}$ in ek is only
       available for $I_{mid}$.

       Here instead we use $g^{\beta_v v_{mid}(s)}$
    *)
    let b_vvsb_wwsb_yys (* $g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)}$ *) =
      (* $g^{\beta_v v(s) + \beta_w w(s) + \beta_y y(s)}
         = g^{\beta_v v(s)} + g^{\beta_w w(s)} + g^{\beta_y y(s)}$ *)
      let open G1 in
      sum
        [ sum_map_g1 imid (* !!! different from the paper !!! *) (fun k ->
              let b_vv_ks = b_vv_ks #! k in
              let c_k = c #! k in
              b_vv_ks * Fr.of_int c_k);
          sum_map_g1 m (fun k ->
              let b_ww_ks = b_ww_ks #! k in
              let c_k = c #! k in
              b_ww_ks * Fr.of_int c_k);
          sum_map_g1 m (fun k ->
              let b_yy_ks = b_yy_ks #! k in
              let c_k = c #! k in
              b_yy_ks * Fr.of_int c_k) ]
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

  type vkey = KeyGen(C).vkey
  type proof = Compute(C).proof

  let f (vkey : vkey) (ios : int Var.Map.t) (proof : proof) =
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

    (* KC check
       $v_{mid}(s)$ is really a linear combination of $\{v_k(s)\}$.
       Actually, $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$  *)
    assert (
        e proof.v_mids vkey.a
        = e proof.av_mids vkey.one
      );

    (* KC check
       $w(s)$ is really a linear combination of $\{w_k(s)\}$.
       Actually, $w(s) = \Sigma_{k\in [m]} c_k \cdot w_k(s)$ *)
    assert (
        e proof.ws vkey.a
        = e proof.aws vkey.one
      );

    (* KC check
       $y(s)$ is really a linear combination of $\{y_k(s)\}$.
       Actually, $y(s) = \Sigma_{k\in [m]} c_k \cdot y_k(s)$ *)
    assert (
        e proof.ys vkey.a
        = e proof.ays vkey.one
      );

    (* KC check
       $h(s)$ is really a linear combination of $\{s^i\}$.
       Actually, $h(s) = a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d$ *)
    assert (
        e proof.hs vkey.a
        = e proof.ahs vkey.one
      );

    (* KC check
       $g^{\beta_vv_{mid}(s)+\beta_ww(s)+\beta_yy(s)}$ is really a linear combination of
       $\{g^{\beta_v v_k(s)}\}$, $\{g^{\beta_v v_k(s)}\}$, and $\{g^{\beta_v v_k(s)}\}$.
       Actually, $h(s) = a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d$ *)
    assert (
        e proof.b_vvsb_wwsb_yys vkey.g

        = e proof.v_mids vkey.b_vg
          + e proof.ws vkey.b_wg
          + e proof.ys vkey.b_yg
      );

    let c = ios in (* $Dom(c) = [N]$ *)

    let sum_fold_g1 map f =
      (* $ \Sigma_{k\in Dom(map)} f(k,map(k)) $ *)
      let open G1 in
      Var.Map.fold (fun k v acc -> f k v + acc) map zero
    in

    let v_ios (* $g^{v_{io}(s)}$ *) =
      (* $\Pi_{k\in [N]} (g^{v_k(s)})^{c_k}$

         $(g^{v_k(s)})^{c_k} = g^{v_k(s) \cdot c_k}$
      *)
      let open G1 in
      sum_fold_g1 c @@ fun k c_k ->
          let v_ks = vkey.v_ks #! k in
          v_ks * Fr.of_int c_k
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
        e G1.(v_ios + proof.v_mids) proof.ws_g2
        - e proof.ys vkey.one

        = e proof.hs vkey.ts
      )
end

module ZKCompute(C : CURVE) = struct
  open C

  module Poly = Polynomial.Make(Fr)

  type ekey = KeyGen(C).ekey

  type proof =
    { v_mids : G1.t; (* $g^{v_{mid}(s)}$ *)
      ws : G1.t; (* $g^{w(s)}$ *)
      ws_g2 : G2.t; (* $g^{w(s)}$ *)
      ys : G1.t; (* $g^{y(s)}$ *)
      hs : G1.t; (* $g^{h(s)}$ *)
      av_mids : G1.t; (* $g^{\alpha v_{mid}(s)}$ *)
      aws : G1.t; (* $g^{\alpha w(s)}$ *)
      ays : G1.t; (* $g^{\alpha y(s)}$ *)
      ahs : G1.t; (* $g^{\alpha h(s)}$ *)
      b_vvsb_wwsb_yys : G1.t; (* $g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)}$ *)

      v_z_mids : G1.t; (* $g^{v_z_{mid}(s)}$ *)
      w_zs_g2 : G2.t; (* $g^{w_z(s)}$ *)
      y_zs : G1.t; (* $g^{y_z(s)}$ *)
      h_zs : G1.t; (* $g^{h_z(s)}$ *)
    }

  let sum_map_g1 set f =
    (* $ \Sigma_{k\in set} f(k) $ *)
    let open G1 in
    Var.Set.fold (fun v acc -> f v + acc) set zero

  let sum_map_g2 set f =
    (* $ \Sigma_{k\in set} f(k) $ *)
    let open G2 in
    Var.Set.fold (fun v acc -> f v + acc) set zero

  let f rng (target : Poly.t) (ekey : ekey) (circuit : Circuit.t) (sol : int Var.Map.t) (h : Poly.t) =

    (* Now $I_{mid}$ should carry the inputs *)
    let imid (* $I_{mid}$ *) = circuit.mids in
    let m (* $[m]$ *) = Circuit.vars circuit.gates in
    let
      { v_ks;
        v_ks_m;
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
        s'i_g2 = _;
        as'i;
      } : ekey = ekey
    in
    let c = sol in

    let v_mids (* $g^{v_{mid}(s)}$ *) =
      (* $v_{mid}(x) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(x)$

         $g^{v_{mid}(s)} = g^{\Sigma_{k\in I_{mid}} c_k \cdot v_k(s)}$
                       $= g^{c_k_i \cdot v_k_i(s)} + .. + g^{c_k_j \cdot v_k_j(s)}$
                       $= g^{v_k_i(s)} \cdot c_k_i + .. + g^{v_k_j(s)} \cdot c_k_j$
                       $= \Sigma_{k\in I_{mid}} ( g^{v_k(s)} * c_k)$
           *)
      let open G1 in
      sum_map_g1 imid @@ fun k ->
          let v_ks = v_ks #! k in
          let c_k = c #! k in
          v_ks * Fr.of_int c_k
    in
    let ws (* $g^{w(s)}$ *) =
      (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

         $g^{w(s)} = \Sigma_{k\in [m]} ( g^{w_k(s)} \cdot c_k )$
      *)
      let open G1 in
      sum_map_g1 m @@ fun k ->
          let w_ks = w_ks #! k in
          let c_k = c #! k in
          w_ks * Fr.of_int c_k
    in
    let ws_g2 (* $g^{w(s)}$ *) =
      (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

         $g^{w(s)} = \Sigma_{k\in [m]} ( g^{w_k(s)} \cdot c_k )$
      *)
      let open G2 in
      sum_map_g2 m @@ fun k ->
          let w_ks = w_ks_g2 #! k in
          let c_k = c #! k in
          w_ks * Fr.of_int c_k
    in
    let ys (* $g^{y(s)}$ *) =
      (* $y(x) = \Sigma_{k\in [m]} c_k \cdot y_k(x)$

         $g^{y(s)} = \Sigma_{k\in [m]} ( g^{y_k(s)} \cdot c_k )$
      *)
      let open G1 in
      sum_map_g1 m @@ fun k ->
          let y_ks = y_ks #! k in
          let c_k = c #! k in
          y_ks * Fr.of_int c_k
    in
    let hs (* $g^{h(s)}$ *) =
      (* $h(s) = a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d$
         $g^{h(s)} = g^{a_0 + a_1 * s + a_2 * s^2 + .. + a_d * s^d}$
                   $= g^{a_0} + g^{s * a_1} + g^{s^2 * a_2} + .. + g^{s^d * a_d}$
      *)
      let open G1 in
      sum @@
      List.mapi (fun i ai ->
          let s'i = List.assoc i s'i in
          s'i * ai) h
    in
    let av_mids (* $g^{\alpha v_{mid}(s)}$ *) =
      (* $g^{\alpha v_{mid}(s)} = g^{\Sigma_{k\in I_{mid}} c_k \alpha v_k(s)}$
                       $= \Sigma_{k\in I_{mid}} ( g^{\alpha v_k(s)}\cdot c_k )$
      *)
      let open G1 in
      sum_map_g1 imid @@ fun k ->
          let av_ks = av_ks #! k in
          let c_k = c #! k in
          av_ks * Fr.of_int c_k
    in
    let aws (* $g^{\alpha w(s)}$ *) =
      (* $w(x) = \Sigma_{k\in [m]} c_k \cdot w_k(x)$

         $g^{\alpha w(s)} = \Sigma_{k\in [m]} ( g^{\alpha w_k(s)} \cdot c_k )$
      *)
      let open G1 in
      sum_map_g1 m @@ fun k ->
          let aw_ks = aw_ks #! k in
          let c_k = c #! k in
          aw_ks * Fr.of_int c_k
    in
    let ays (* $g^{\alpha y(s)}$ *) =
      let open G1 in
      sum_map_g1 m @@ fun k ->
          let ay_ks = ay_ks #! k in
          let c_k = c #! k in
          ay_ks * Fr.of_int c_k
    in
    let ahs (* $g^{\alpha h(s)}$ *) =
      (* $h(s) = a_0 + a_1 * s + a_2 * s^2 + .. + a_d * s^d$
         $g^{\alpha h(s)} = g^{\alpha (a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d)}$
                  $= g^1 \cdot a_0 + g^{\alpha s} \cdot a_1 + g^{\alpha s^2} * a_2 + .. + g^{\alpha s^d} \cdot a_d$
      *)
      let open G1 in
      sum @@
      List.mapi (fun i ai ->
          let as'i = List.assoc i as'i in
          as'i * ai) h
    in

    (* Bug of the paper?

       $g^{\beta_v v(s)}$  is not computable since $g^{\beta_v v_k(s)}$ in ek is only
       available for $I_{mid}$.

       Here instead we use $g^{\beta_v v_{mid}(s)}$
    *)
    let b_vvsb_wwsb_yys (* $g^{\beta_vv(s)+\beta_ww(s)+\beta_yy(s)}$ *) =
      (* $g^{\beta_v v(s) + \beta_w w(s) + \beta_y y(s)}
         = g^{\beta_v v(s)} + g^{\beta_w w(s)} + g^{\beta_y y(s)}$ *)
      let open G1 in
      sum
        [ sum_map_g1 imid (* !!! different from the paper !!! *) (fun k ->
              let b_vv_ks = b_vv_ks #! k in
              let c_k = c #! k in
              b_vv_ks * Fr.of_int c_k);
          sum_map_g1 m (fun k ->
              let b_ww_ks = b_ww_ks #! k in
              let c_k = c #! k in
              b_ww_ks * Fr.of_int c_k);
          sum_map_g1 m (fun k ->
              let b_yy_ks = b_yy_ks #! k in
              let c_k = c #! k in
              b_yy_ks * Fr.of_int c_k) ]
    in

    (* ZK *)

    let d_v (* $\delta_v$ *) = Fr.gen rng in
    let d_w (* $\delta_w$ *) = Fr.gen rng in
    let d_y (* $\delta_y$ *) = Fr.gen rng in
    let dts d (* $g^{\delta t(s)}$ *) =
      (* $t(s) = t_0 s^0 + t_1 s^1 + .. + t_d s^d$ *)
      let open G1 in
      sum @@
      List.mapi (fun j t_j ->
          let s'j (* $g^{s^j}$ *) = List.assoc j ekey.s'i in
          s'j * Fr.(d * t_j) (* $g^{\delta t_j s^j}$ *)
        ) target
    in
    let dts_g2 d (* $g^{\delta t(s)}$ *) =
      (* $t(s) = t_0 s^0 + t_1 s^1 + .. + t_d s^d$ *)
      let open G2 in
      sum @@
      List.mapi (fun j t_j ->
          let s'j (* $g^{s^j}$ *) = List.assoc j ekey.s'i_g2 in
          s'j * Fr.(d * t_j) (* $g^{\delta t_j s^j}$ *)
        ) target
    in

    (*
       $p_z(x) := (\Sigma c_k v_k(x) + \delta_v t(x))
                   \cdot (\Sigma c_k w_k(x) + \delta_w t(x))
                   - (\Sigma c_k y_k(x) + \delta_y t(x))$
           $= (\Sigma c_k v_z(x)) \cdot (\Sigma c_k w_z(x)) - \Sigma c_k y_k(x)
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

       $h_z(x) := h(x) + (\Sigma c_k v_k(x)) \cdot \delta_w
                       + (\Sigma c_k w_k(x)) \cdot \delta_v
                       + \delta_v \delta_w t(x)
                       - \delta_y$

       $p_z(x) = h_z(x) \cdot t(x)$
    *)

    let vs (* $g^{v(s)}$ *) =
      let open G1 in
      sum_map_g1 m @@ fun k ->
          let v_ks = v_ks_m #! k in
          let c_k = c #! k in
          v_ks * Fr.of_int c_k
    in

    let h_zs (* $g^{h_z(s)}$ *) =
      (* $h(s) = a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d$
         $h_z(x) = h(x) + (\Sigma c_k v_k(x)) \cdot \delta_w
                   + (\Sigma c_k w_k(x)) \cdot \delta_v
                   + \delta_v \delta_w t(x)
                   - \delta_y$
         $g^{h_z(s)} = g^{h(s)}
                       + g^{v(s)} \cdot \delta_w + g^{w(s)} \cdot \delta_v + g^{\delta_v \delta_w t(s)} - g^{\delta_y}$
      *)
      (* Here we absolutely need $v(s) = \Sigma_{k\in [m]} c_k \cdot v_k(s)$, missing in the original ek *)
      let open G1 in
      let hs (* $g^{h(s)}$ *) =
        sum @@
        List.mapi (fun i ai ->
            let s'i = List.assoc i s'i in
            s'i * ai) h
      in
      let d_vd_wts (* $\delta_v \delta_w t(s)$ *) =
        dts Fr.(d_v * d_w)
      in
      hs + vs * d_w + ws * d_v + d_vd_wts - of_Fr d_y
    in

    let v_z_mids (* $g^{v_z_{mid}(s)}$ *) =
      (* It must include $\delta_v t(s)$ since the verifier does no know $\delta_v$. *)
      (* $v_z_{mid}(s) = v_{mid}(s) + \delta_v t(s)$ *)
      let open G1 in
      v_mids + dts d_v
    in

    let w_zs_g2 (* $g^{w_z(s)}$ *) =
      (* $w_z(s) = w(s) + \delta_w t(s)$ *)
      let open G2 in
      ws_g2 + dts_g2 d_w
    in

    let y_zs (* $g^{y_z(s)}$ *) =
      (* $y_z(s) = y(s) + \delta_y t(s)$ *)
      let open G1 in
      ys + dts d_y
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

      v_z_mids;
      w_zs_g2;
      y_zs;
      h_zs
    }

end

module ZKVerify(C : CURVE) = struct
  open C

  type vkey = KeyGen(C).vkey
  type proof = ZKCompute(C).proof

  let sum_fold_g1 map f =
    (* $ \Sigma_{k\in Dom(map)} f(k,map(k)) $ *)
    let open G1 in
    Var.Map.fold (fun k v acc -> f k v + acc) map zero

  let f (vkey : vkey) (ios : int Var.Map.t) (proof : proof) =
    let e = Pairing.pairing in
    let open GT in

    (* KC check
       $v_{mid}(s)$ is really a linear combination of $\{v_k(s)\}$.
       Actually, $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$  *)
    assert (
        e proof.v_mids vkey.a
        = e proof.av_mids vkey.one
      );

    (* KC check
       $w(s)$ is really a linear combination of $\{w_k(s)\}$.
       Actually, $w(s) = \Sigma_{k\in [m]} c_k \cdot w_k(s)$ *)
    assert (
        e proof.ws vkey.a
        = e proof.aws vkey.one
      );

    (* KC check
       $y(s)$ is really a linear combination of $\{y_k(s)\}$.
       Actually, $y(s) = \Sigma_{k\in [m]} c_k \cdot y_k(s)$ *)
    assert (
        e proof.ys vkey.a
        = e proof.ays vkey.one
      );

    (* KC check
       $h(s)$ is really a linear combination of $\{s^i\}$.
       Actually, $h(s) = a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d$ *)
    assert (
        e proof.hs vkey.a
        = e proof.ahs vkey.one
      );

    (* KC check
       $g^{\beta_vv_{mid}(s)+\beta_ww(s)+\beta_yy(s)}$ is really a linear combination of
       $\{g^{\beta_v v_k(s)}\}$, $\{g^{\beta_v v_k(s)}\}$, and $\{g^{\beta_v v_k(s)}\}$.
       Actually, $h(s) = a_0 + a_1  s + a_2  s^2 + .. + a_d  s^d$ *)
    assert (
        e proof.b_vvsb_wwsb_yys vkey.g

        = e proof.v_mids vkey.b_vg
          + e proof.ws vkey.b_wg
          + e proof.ys vkey.b_yg
      );

    let c = ios in (* $Dom(c) = [N]$ *)

    let v_ios (* $g^{v_{o}(s)}$ *) =
      (* $\Pi_{k\in [N]} (g^{v_k(s)})^{c_k}$

         $(g^{v_k(s)})^{c_k} = g^{v_k(s) \cdot c_k}$
      *)
      let open G1 in
      sum_fold_g1 c @@ fun k c_k ->
          let v_ks = vkey.v_ks #! k in
          v_ks * Fr.of_int c_k
    in
    (*A final check (with 3 pairings) verifies the divisibility requirement, i.e.,
      that $e(g^{v_0(s)} \cdot g^{v_{io}} \cdot g^{v_z_{mid}(s)},~
              g^{w_0(s)} \cdot g^{w_z(s)})
            ~/~ e (g^{y_0(s)} \cdot g^{y_z(s)},~ g)$
            $= e (g^{h_z(s)},~ g^{t(s)}) $
    *)
    (* In our implementation, $v_0(s), w_0(s), y_0(s)$ are in $v_{io}(s)$ *)
    (* Here is to prove $p_z(s) = h_z(s) \cdot t(s)$.

       LHS:
       $e(g^{v_0(s)} \cdot g^{v_{io}} \cdot g^{v_z_{mid}(s)},~
            g^{w_0(s)} \cdot g^{w_z(s)})
          = e(g^{v_0(s)} \cdot g^{v_z(s)},~g^{w_0(s)} \cdot g^{w_z(s)})$
              $= e(g^{(v_0(s) + v_z(s)) \cdot (w_0(s) + w_z(s))}, g^1)$
              $= e(g^{p_z(s)}, g^1)$

       RHS:
       $e (g^{h_z(s)},~ g^{t(s)})$
    *)
    assert (
        e G1.(v_ios + proof.v_z_mids) proof.w_zs_g2
        - e proof.y_zs vkey.one

        = e proof.h_zs vkey.ts
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
  let rng = Random.State.make_self_init () in
  let module KeyGen = KeyGen(C) in
  let module Compute = Compute(C) in
  let module Verify = Verify(C) in
  let module ZKCompute = ZKCompute(C) in
  let module ZKVerify = ZKVerify(C) in
  let prepare e =
    let circuit = Circuit.of_expr e in
    let qap = QAP.build circuit.gates in
    circuit, qap
  in
  let circuit, qap = prepare e in
  let ek, vk = KeyGen.generate rng circuit qap in
  let proof =
    let sol = Result.get_ok @@ Circuit.eval [x, 3; Circuit.one, 1] circuit.gates in
    let _p, h = QAP.eval sol qap in
    Compute.f ek circuit (Var.Map.of_seq @@ List.to_seq sol) h
  in
  let () =
    let ios = Circuit.ios circuit in
    assert (Var.Set.equal ios (Var.Set.of_list [x; Circuit.one; Circuit.out]));
    let input = [x, 3; Circuit.one, 1] in
    let output = [Circuit.out, 18] in
    Verify.f vk (Var.Map.of_seq @@ List.to_seq (input @ output)) proof
  in

  let zcircuit = { circuit with mids = Var.Set.add x circuit.mids } in
  let ek, vk = KeyGen.generate rng zcircuit qap in
  let zkproof =
    let sol = Result.get_ok @@ Circuit.eval [x, 3; Circuit.one, 1] circuit.gates in
    let _p, h = QAP.eval sol qap in
    (* hide x *)
    ZKCompute.f rng qap.target ek zcircuit (Var.Map.of_seq @@ List.to_seq sol) h
  in
  let () =
    let ios = Circuit.ios zcircuit in
    assert (Var.Set.equal ios (Var.Set.of_list [Circuit.one; Circuit.out]));
    let input = [Circuit.one, 1] in
    let output = [Circuit.out, 18] in
    ZKVerify.f vk (Var.Map.of_seq @@ List.to_seq (input @ output)) zkproof
  in
  prerr_endline "PROTOCOL TEST done!"

let test () =
  let module QAP = QAP(Q) in
  QAP.test ();
  protocol_test ()
