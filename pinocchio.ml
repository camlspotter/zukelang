(* This code implements Protocol 2 described in https://eprint.iacr.org/2013/279.pdf

   Protocol 1 is not for ordinary QAP.
*)

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

    val pp : t printer
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

  val build : Circuit.Gate.t Var.Map.t -> t * F.t Var.Map.t

  val decompile : t -> F.t Var.Map.t -> (Var.t * ( (Var.t * F.t) list * (Var.t * F.t) list )) list
  val eval : (Var.t * int) list -> t -> F.t Polynomial.t * F.t Polynomial.t
  (** compute $p$ and $h$ *)

  val test : unit -> unit

end = struct

  module Poly = Polynomial.Make(F)

  type t =
    { vwy : F.t Polynomial.t Var.Map.t vwy;
      target : F.t Polynomial.t
    }

  let build (gates : Circuit.Gate.t Var.Map.t) =
    let rk =
      List.mapi (fun i (v, _) ->
          Format.eprintf "gate %a : r_%a = %d@."
            Var.pp v Var.pp v i;
          v,i) @@ Var.Map.bindings gates in
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

    { vwy = { v; w; y }; target = t },
    Var.Map.of_seq @@ List.to_seq @@ List.map (fun (v, i) -> v, F.of_int i) rk

  let decompile {vwy= { v; w; y }; _} (rs : F.t Var.Map.t) =
    let dom m =
      Var.Set.of_seq @@ Seq.map fst @@ Var.Map.to_seq m
    in
    let domv = dom v in
    let domw = dom w in
    let domy = dom y in
    assert (Var.Set.equal domv domw);
    assert (Var.Set.equal domv domy);
    Format.(ef "dom: @[%a@]@." (list ",@ " Var.pp) (Var.Set.elements domv));
    Var.Map.fold (fun g r acc ->
        let f v =
          List.filter_map (fun (v, p) ->
              let w = Poly.apply p r in
              if F.(w = zero) then None
              else Some (v, w))
          @@
          Var.Map.bindings v
        in
        let v = f v in
        let w = f w in
        let y = f y in
        let pp = Format.(list " + " (fun ppf (v,i) -> f ppf "%a%a" F.pp i Var.pp v)) in
        Format.ef "Gate %a : %a = (%a) * (%a)@." Var.pp g pp y pp v pp w;
        match y with
        | [y, f] when F.(one = f) -> (y, (v, w)) :: acc
        | _ -> assert false
      ) rs []

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
    let ({ vwy; target= t } as qap), _rk = build circuit.gates in
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

  module QAP = QAP(Fr)

  (* $ \Sigma_{k\in Dom(m)} f(k,m_k) $ *)
  let sum_map (type t) (module G : G with type t = t) m f =
    let open G in
    Var.Map.fold (fun k v acc -> f k v + acc) m zero

  (* $ \Sigma_{k\in Dom(m)} m_k \cdot c_k$ *)
  let dot (type t) (module G : G with type t = t) m c =
    if not (Var.Set.equal (Var.Map.domain m) (Var.Map.domain c)) then begin
      prerr_endline "Domain mismatch";
      Format.(ef "m : %a@.c : %a@." Var.Set.pp (Var.Map.domain m) Var.Set.pp (Var.Map.domain c));
      assert false
    end;
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

  (* $\{\alpha x_k\}_k$ *)
  let mul_map (type t) (module G : G with type t = t) m a = Var.Map.map (fun g -> G.(g * a)) m

  module KeyGen = struct

    (* The paper uses symmetric groups: e : $G_1 = G_2$.  Here we use BLS12-381
       with assymmetric groups $G_1 \neq G_2$.  Therefore some fields require values
       in $G_2$ too.
    *)
    type ekey =
      { v    : G1.t Var.Map.t; (* $\{ g_v^{v_k(s)} \}_{k\in I_{mid}}$ *)
        w    : G2.t Var.Map.t; (* $\{ g_w^{w_k(s)} \}_{k\in I_{mid}}$ *)
        y    : G1.t Var.Map.t; (* $\{ g_y^{y_k(s)} \}_{k\in I_{mid}}$ *)
        av   : G1.t Var.Map.t; (* $\{ g_v^{\alpha_v v_k(s)} \}_{k\in I_{mid}}$ *)
        aw   : G2.t Var.Map.t; (* $\{ g_w^{\alpha_y w_k(s)} \}_{k\in I_{mid}}$ *)
        ay   : G1.t Var.Map.t; (* $\{ g_y^{\alpha y_k(s)} \}_{k\in I_{mid}}$ *)
        s'i  : (int * G1.t) list; (* $\{ g_1^{s^i} \}_{i\in[d]}$ *)
        bvwy : G1.t Var.Map.t; (* $\{ g_v^{\beta v_k(s)} g_w^{\beta w_k(s)} g_y^{\beta y_k(s)} \}_{k\in I_{mid}}$ *)

        (* Required for ZK *)
        s'i2 : (int * G2.t) list; (* $\{ g_1^{s^i} \}_{i\in[d]}$ *)
        vt : G1.t; (* $g_v^{t(s)}$ *)
        wt : G2.t; (* $g_w^{t(s)}$ *)
        yt : G1.t; (* $g_y^{t(s)}$ *)
        avt : G1.t; (* $g_v^{\alpha_v t(s)}$ *)
        awt : G2.t; (* $g_w^{\alpha_y t(s)}$ *)
        ayt : G1.t; (* $g_y^{\alpha_w t(s)}$ *)
        vbt : G1.t;  (* $g_v^{\beta t(s)}$ *)
        wbt : G1.t;  (* $g_w^{\beta t(s)}$ *)
        ybt : G1.t;  (* $g_y^{\beta t(s)}$ *)
        v_all : G1.t Var.Map.t; (* $\{ g_1^{v_k(s)} \}_{k\in [N]}$ Not $g_v^{v_k(s)}$!! *)
        w_all : G1.t Var.Map.t; (* $\{ g_1^{w_k(s)} \}_{k\in [N]}$ Not $g_w^{v_k(s)}$!! *)
     }

    type vkey =
      { one    : G1.t; (* $g^1$ *)
        one2 : G2.t; (* $g^1$ *)
        av     : G2.t; (* $g^{\alpha_v}$ *)
        aw     : G1.t; (* $g^{\alpha_w}$ *)
        ay     : G2.t; (* $g^{\alpha_y}$ *)
        gm2    : G2.t; (* $g^\gamma$ *)
        bgm    : G1.t; (* $g^{\beta\gamma}$ *)
        bgm2   : G2.t; (* $g^{\beta\gamma}$ *)
        t      : G2.t; (* $g_y^{t(s)}$ *)
        v      : G1.t Var.Map.t; (* $\{ g_v^{v_k(s)} \}_{k\in [N]}$ *)
        w      : G2.t Var.Map.t; (* $\{ g_w^{w_k(s)} \}_{k\in [N]}$ *)
        y      : G1.t Var.Map.t; (* $\{ g_y^{y_k(s)} \}_{k\in [N]}$ *)
      }

    let generate rng (circuit : Circuit.t) QAP.{vwy; target= t} =
      let imid (* $I_{mid}$ *) = circuit.mids in
      let n (* $[N]$ *) = Circuit.ios circuit in
      let m (* [m] *) = Circuit.vars circuit.gates in
      let d = Poly.degree t in

      let rv (* $r_v$ *)      = Fr.gen rng in
      let rw (* $r_w$ *)      = Fr.gen rng in
      let s (* $s$ *)         = Fr.gen rng in
      let av (* $\alpha_v$ *) = Fr.gen rng in
      let aw (* $\alpha_w$ *) = Fr.gen rng in
      let ay (* $\alpha_y$ *) = Fr.gen rng in

      (* nasty *)
      let _av = av and _aw = aw and _ay = ay in

      let b (* $\beta$ *)     = Fr.gen rng in
      let gm (* $\gamma$ *)     = Fr.gen rng in

      let ry (* $r_y$ *)      = Fr.(rv * rw) in

      let gv (* $g_v$ *) = G1.of_Fr rv in
      let gw (* $g_w$ *) = G1.of_Fr rw in
      let gw2 = G2.of_Fr rw in
      let gy (* $g_y$ *) = G1.of_Fr ry in
      let gy2 = G2.of_Fr ry in

      (* nasty *)
      let _t = Poly.apply t s in

      (* $\{ g_u^{u_k(s)} \}_{k\in I_{set}}$ *)
      let map_apply_s (type t) (module G : G with type t = t) gu u set =
        Var.Map.of_set set @@ fun k ->
        let uk = u #! k in
        let uks = Poly.apply uk s in
        G.(gu * uks)
      in

      let ekey =
        (* $\{ g_v^{v_k(s)} \}_{k\in I_{mid}}$ *)
        let v = map_apply_s g1 gv vwy.v imid in
        (* $\{ g_w^{w_k(s)} \}_{k\in I_{mid}}$ *)
        let w1 = map_apply_s g1 gw vwy.w imid in
        let w = map_apply_s g2 gw2 vwy.w imid in
        (* $\{ g_y^{y_k(s)} \}_{k\in I_{mid}}$ *)
        let y = map_apply_s g1 gy vwy.y imid in

        (* $\{ g_v^{\alpha_v v_k(s)} \}_{k\in I_{mid}}$ *)
        let av = mul_map g1 v av in
        (* $\{ g_w^{\alpha_w w_k(s)} \}_{k\in I_{mid}}$ *)
        let aw = mul_map g2 w aw in
        (* $\{ g_y^{\alpha_y y_k(s)} \}_{k\in I_{mid}}$ *)
        let ay = mul_map g1 y ay in

        (* $\{ g^s^i \}_{i\in[d]}$ *)
        let s'i = powers g1 d s in
        let s'i2 = powers g2 d s in

        (* $\{ g_v^{\beta v_k(s)} g_w^{\beta w_k(s)} g_y^{\beta y_k(s)} \}_{k\in I_{mid}}$ *)
        let bvwy =
          Var.Map.of_set imid @@ fun k ->
          G1.( ((v #! k) + (w1 #! k) + (y #! k)) * b )
        in

        let vt (* $g_v^{\alpha_v t(s)}$ *) = G1.(gv * _t) in
        let wt (* $g_w^{\alpha_w t(s)}$ *) = G2.(gw2 * _t) in
        let yt (* $g_y^{\alpha_y t(s)}$ *) = G1.(gy * _t) in
        let avt (* $g_v^{\alpha_v t(s)}$ *) = G1.(gv * _av * _t) in
        let awt (* $g_w^{\alpha_w t(s)}$ *) = G2.(gw2 * _aw * _t) in
        let ayt (* $g_y^{\alpha_y t(s)}$ *) = G1.(gy * _ay * _t) in
        let vbt (* $g_v^{\beta t(s)}$ *) = G1.(gv * b * _t) in
        let wbt (* $g_w^{\beta t(s)}$ *) = G1.(gw * b * _t) in
        let ybt (* $g_y^{\beta t(s)}$ *) = G1.(gy * b * _t) in

        (* $\{ g_1^{v_k(s)} \}_{k\in [m]$ *)
        let v_all = map_apply_s g1 G1.one vwy.v m in

        (* $\{ g_1^{w_k(s)} \}_{k\in [m]$ *)
        let w_all = map_apply_s g1 G1.one vwy.w m in

        { v; w; y; av; aw; ay; s'i; bvwy;
          s'i2; vt; wt; yt; avt; awt; ayt; vbt; wbt; ybt; v_all; w_all }
      in

      let vkey =
        let one (* $g^1$ *) = G1.one in
        let one2 (* $g^1$ *) = G2.one in
        let av (* $g^\alpha_v$ *) = G2.of_Fr av in
        let aw (* $g^\alpha_w$ *) = G1.of_Fr aw in
        let ay (* $g^\alpha_y$ *) = G2.of_Fr ay in
        let gm, gm2 (* $g^\gamma$ *) = G1.of_Fr gm, G2.of_Fr gm in
        let bgm (* $g^{\beta\gamma}$ *) = G1.(gm * b) in
        let bgm2 (* $g^{\beta\gamma}$ *) = G2.(gm2 * b) in
        let t (* $g_y^{t(s)}$ *) = G2.(gy2 * (Poly.apply t s)) in
        let v (* $\{g_v^{v_k(s)}\}_{k\in [N]}$ *) = map_apply_s g1 gv vwy.v n in
        let w (* $\{g_w^{w_k(s)}\}_{k\in [N]}$ *) = map_apply_s g2 gw2 vwy.w n in
        let y (* $\{g_y^{y_k(s)}\}_{k\in [N]}$ *) = map_apply_s g1 gy vwy.y n in
        { one;
          one2;
          av;
          aw;
          ay;
          gm2;
          bgm;
          bgm2;
          t;
          v;
          w;
          y }
      in

      ekey, vkey

  end

  module Compute = struct

    type proof =
      { v  : G1.t; (* $g_v^{v_{mid}(s)}$ *)
        w  : G2.t; (* $g_w^{w_{mid}(s)}$ *)
        y  : G1.t; (* $g_y^{y_{mid}(s)}$ *)

        h  : G1.t;  (* $g^{h(s)}$ *)

        av : G1.t; (* $g_v^{\alpha_v v_{mid}(s)}$ *)

        aw : G2.t; (* $g_w^{\alpha_w w_{mid}(s)}$ *)
        ay : G1.t; (* $g_y^{\alpha_y y_{mid}(s)}$ *)

        bvwy : G1.t; (* $g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}$ *)
      }

    let f (ekey : KeyGen.ekey) (sol : Fr.t Var.Map.t) (h_poly : Poly.t) =
      let c = sol in
      let mid = Var.Map.domain ekey.v in
      let c_mid = Var.Map.filter (fun v _ -> Var.Set.mem v mid) c in

     Format.(ef "Compute for @[%a@]@."
                (list ",@ " (fun ppf (v,n) -> f ppf "%a = %a" Var.pp v Fr.pp n))
                (List.of_seq @@ Var.Map.to_seq c));

      (* $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$ *)
      let v (* $g_v^{v_{mid}(s)}$ *) = dot g1 ekey.v c_mid in

      (* $w(s) = \Sigma_{k\in [m]} c_k \cdot w_k(s)$ *)
      let w (* $g_w^{w_{mid}(s)}$ *) = dot g2 ekey.w c_mid in

      (* $y(s) = \Sigma_{k\in [m]} c_k \cdot y_k(s)$ *)
      let y (* $g_y^{y_{mid}(s)}$ *) = dot g1 ekey.y c_mid in

      (* $h(s) = h_0 + h_1  s + h_2  s^2 + .. + h_d  s^d$ *)
      let h (* $g^{h(s)}$ *) = apply_powers g1 h_poly ekey.s'i in

      (* $\alpha_v v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_v v_k(s)$ *)
      let av (* $g_v^{\alpha v_{mid}(s)}$ *) = dot g1 ekey.av c_mid in

      (* $\alpha_w w_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_w w_k(s)$ *)
      let aw (* $g_w^{\alpha_w w_{mid}(s)}$ *) = dot g2 ekey.aw c_mid in

      (* $\alpha_y y_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_y y_k(s)$ *)
      let ay (* $g_y^{\alpha_y y_{mid}(s)}$ *) = dot g1 ekey.ay c_mid in

      let bvwy (* $g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}$ *) =
        dot g1 ekey.bvwy c_mid
      in
      { v;
        w;
        y;
        h;
        av;
        aw;
        ay;
        bvwy;
      }

  end

  module Verify = struct

    let f (vkey : KeyGen.vkey) (ios : Fr.t Var.Map.t) (proof : Compute.proof) =
      let c = ios in (* $Dom(c) = [N]$ *)
      Format.(ef "Verifying for @[%a@]@."
                (list ",@ " (fun ppf (v,n) -> f ppf "%a = %a" Var.pp v Fr.pp n))
                (List.of_seq @@ Var.Map.to_seq c));

      (* $e(g_v^{v_{mid}(s)}, g^{\alpha_v}) = e(g_v^{\alpha_v v_{mid}(s)}, g)$
         $e(g_w^{w_{mid}(s)}, g^{\alpha_w}) = e(g_w^{\alpha_w w_{mid}(s)}, g)$
         $e(g_y^{y_{mid}(s)}, g^{\alpha_y}) = e(g^{\alpha_y y_{mid}(s)}, g)$

         $e(g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}, g^\gamma)$
         $= e(g_v^{\beta v_{mid}(s)}
                + g_w^{\beta w_{mid}(s)}
                + g_y^{\beta y_{mid}(s)}, g^\gamma)$
         $= e(g_v^{v_{mid}(s)}, g^{\beta \gamma})
             + e(g_w^{w_{mid}(s)}, g^{\beta \gamma})
             + e(g_y^{y_{mid}(s)}, g^{\beta \gamma})$
      *)
      let e = Pairing.pairing in
      let open GT in

      (* All the ingredients must be KC checked *)

      (* KC check
         $v_{mid}(s)$ is really a linear combination of $\{v_k(s)\}$.
         Actually, $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$
         $e(g_v^{v_{mid}(s)}, g^{\alpha_v}) = e(g_v^{\alpha_v v_{mid}(s)}, g)$
      *)
      assert (e proof.v vkey.av = e proof.av vkey.one2);

      (* KC check
         $w(s)$ is really a linear combination of $\{w_k(s)\}$.
         Actually, $w(s) = \Sigma_{k\in I_{mid}} c_k \cdot w_k(s)$
         $e(g_w^{w_{mid}(s)}, g^{\alpha_w}) = e(g_w^{\alpha_w w_{mid}(s)}, g)$
      *)
      assert (e vkey.aw proof.w = e vkey.one proof.aw);

      (* KC check
         $y(s)$ is really a linear combination of $\{y_k(s)\}$.
         Actually, $y(s) = \Sigma_{k\in I_{mid}} c_k \cdot y_k(s)$ *)
      assert (e proof.y vkey.ay = e proof.ay vkey.one2);

      (* KC check
         $g_v^{\beta v_{mid}(s)} g_w^{\beta_w_{mid}(s)} g_y^{\beta y_{mid}(s)}$ is really a linear combination of
         $\{g_v^{\beta v_k(s)}\}$, $\{g_w^{\beta w_k(s)}\}$, and $\{g_y^{\beta y_k(s)}\}$.

         This is to check the same $\{c_k\}$ is used to build $v_{mid}(s), w_{mid}(s), y_{mid}(s)$.

         $e(g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}, g^\gamma)$
         $= e(g_v^{\beta v_{mid}(s)}
                + g_w^{\beta w_{mid}(s)}
                + g_y^{\beta y_{mid}(s)}, g^\gamma)$
         $= e(g_v^{v_{mid}(s)}, g^{\beta \gamma})
             + e(g_w^{w_{mid}(s)}, g^{\beta \gamma})
             + e(g_y^{y_{mid}(s)}, g^{\beta \gamma})$
      *)
      assert (
          e proof.bvwy vkey.gm2
          = e proof.v vkey.bgm2
            + e vkey.bgm proof.w
            + e proof.y vkey.bgm2
        );

      let vio (* $g_v^{v_{io}(s)}$ *) =
        (* $g_v^{v_{io}(s)} = \Pi_{k\in [N]} (g_v^{v_k(s)})^{c_k} = \Pi_{k\in [N]} g_v^{v_k(s) \cdot c_k}$
           The paper uses prod for the operaiton of Gi.  Our code uses add instead *)
        assert (Var.Set.equal (Var.Map.domain c) (Var.Map.domain vkey.v));
        sum_map g1 c @@ fun k ck ->
            let vks = vkey.v #! k in
            G1.(vks * ck)
      in

      let wio (* $g_w^{w_{io}(s)}$ *) =
        (* $g_w^{w_{io}(s)} = \Pi_{k\in [N]} (g_w^{w_k(s)})^{c_k} = \Pi_{k\in [N]} g_w^{w_k(s) \cdot c_k}$ *)
        assert (Var.Set.equal (Var.Map.domain c) (Var.Map.domain vkey.w));
        sum_map g2 c @@ fun k ck ->
            let wks = vkey.w #! k in
            G2.(wks * ck)
      in

      let yio (* $g_y^{y_{io}(s)}$ *) =
        (* $g_y^{y_{io}(s)} = \Pi_{k\in [N]} (g_y^{y_k(s)})^{c_k} = \Pi_{k\in [N]} g_y^{y_k(s) \cdot c_k}$ *)
        assert (Var.Set.equal (Var.Map.domain c) (Var.Map.domain vkey.y));
        sum_map g1 c @@ fun k ck ->
            let yks = vkey.y #! k in
            G1.(yks * ck)
      in

      (* A final check (with 3 pairings) verifies the divisibility requirement, i.e.,
         that $e(g_v^{v_0(s)} \cdot g_v^{v_{io}(s)} \cdot g_v^{v_{mid}(s)},~
                g_w^{w_0(s)} \cdot g_w^{w_{io}(s)} \cdot g_w^{w_{mid}(s)}))$
              $= e (g^{h(s)},~ g^{t(s)}) \cdot e (g_y^{y_0(s)} \cdot g_y^{y_{io}(s)} \cdot g_y^{y_{mid}(s)},~ g)$

         Our implementation, $v_0(s), w_0(s), y_0(s)$ are included in $v_{io}(s)$.
      *)
      (* Here is to prove $p(s) = h(s) \cdot t(s)$.

         LHS:
         $e(g_v^{v_0(s)} \cdot g_v^{v_{io}(s)} \cdot g_v^{v_{mid}(s)},~
                g_w^{w_0(s)} \cdot g_w^{w_{io}(s)} \cdot g_w^{w_{mid}(s)}))
              ~/~ e (g_y^{y_0(s)} \cdot g_y^{y_{io}(s)} \cdot g_y^{y_{mid}(s)},~ g)$
         $= e(g^{r_v v(s)}, g^{r_w w(s)} ) / e(g^{r_y y(s)}, g)$
         $= e(g^{r_v r_w v(s) w(s) - (r_y y(s))}, g )$
         $= e(g^{r_y(v(s) w(s) - y(s))}, g )$
         $= e(g^{r_y p(s)}, g )$
         $= e(g_y^{p(s)}, g )$

         RHS:
         $e (g^{h(s)},~ g_y^{t(s)})$
         $= e (g^{r_y h(s) t(s)},~ g)$
         $= e (g_y^{p(s)},~ g)$

      *)
      assert (
        e G1.(vio + proof.v) G2.(wio + proof.w)
        - e G1.(yio + proof.y) vkey.one2
        = e proof.h vkey.t
        )
  end

  module ZKCompute = struct

    open Compute

    let f rng (target : Poly.t) (ekey : KeyGen.ekey) (sol : Fr.t Var.Map.t) (h_poly : Poly.t) =
      let dv (* $\delta_v$ *) = Fr.gen rng in
      let dw (* $\delta_w$ *) = Fr.gen rng in
      let dy (* $\delta_y$ *) = Fr.gen rng in
      let t (* $g_1^{t(s)}$, not $g_y^{t(s)}$! *) = apply_powers g1 target ekey.s'i in

      let c = sol in
      let mid = Var.Map.domain ekey.v in
      let c_mid = Var.Map.filter (fun v _ -> Var.Set.mem v mid) c in

      (* $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$ *)
      let v (* $g_v^{v_{mid}(s)}$ *) = dot g1 ekey.v c_mid in
      let v' (* $g_v^{v_{mid}(s) + \delta_v t(s)}$ *) = G1.(v + ekey.vt * dv) in

      (* $w(s) = \Sigma_{k\in [m]} c_k \cdot w_k(s)$ *)
      let w (* $g_w^{w_{mid}(s)}$ *) = dot g2 ekey.w c_mid in
      let w' (* $g_w^{w_{mid}(s) + \delta_w t(s)}$ *) = G2.(w + ekey.wt * dw) in

      (* $y(s) = \Sigma_{k\in [m]} c_k \cdot y_k(s)$ *)
      let y (* $g_y^{y_{mid}(s)}$ *) = dot g1 ekey.y c_mid in
      let y' (* $g_y^{y_{mid}(s) + \delta_y  t(s)}$ *) = G1.(y + ekey.yt * dy) in

      (* $h(s) = h_0 + h_1  s + h_2  s^2 + .. + h_d  s^d$ *)
      let h (* $g^{h(s)}$ *) = apply_powers g1 h_poly ekey.s'i in
      (* $p'(x) := v'(x) \cdot w'(x) - y'(x)$
             $= (\Sigma c_k v_k(x) + \delta_v t(x))\cdot (\Sigma c_k w_k(x) + \delta_w t(x))
                     - (\Sigma c_k y_k(x) + \delta_y t(x))$
             $= (\Sigma c_k v(x)) \cdot (\Sigma c_k w(x)) - \Sigma c_k y_k(x)
                  + (\Sigma c_k v_k(x)) \cdot \delta_w t(x)
                  + (\Sigma c_k w_k(x)) \cdot \delta_v t(x)
                  + \delta_v \delta_w (t(x))^2
                  - \delta_y t(x)$
             $= p(x)
                  + (\Sigma c_k v_k(x)) \cdot \delta_w t(x)
                  + (\Sigma c_k w_k(x)) \cdot \delta_v t(x)
                  + \delta_v \delta_w (t(x))^2
                  - \delta_y t(x)$
             $= h(x) \cdot t(x)
                  + (\Sigma c_k v_k(x)) \cdot \delta_w t(x)
                  + (\Sigma c_k w_k(x)) \cdot \delta_v t(x)
                  + \delta_v \delta_w (t(x))^2
                  - \delta_y t(x)$
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
        let v_all (* $g_1^{v(s)}$ Not $g_v^{v(s)}$!! *) = dot g1 ekey.v_all c in
        let w_all (* $g_1^{w(s)}$ Not $g_w^{w(s)}$!! *) = dot g1 ekey.w_all c in
        h  +  v_all * dw  +  w_all * dv  +  t * dv * dw  -  one * dy
      in

      (* $\alpha_v v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_v v_k(s)$ *)
      let av (* $g_v^{\alpha v_{mid}(s)}$ *) = dot g1 ekey.av c_mid in
      let av' (* $g_v^{\alpha (v_{mid}(s) + \delta_v t(s))}$ *) = G1.(av + ekey.avt * dv) in

      (* $\alpha_w w_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_w w_k(s)$ *)
      let aw (* $g_w^{\alpha_w w_{mid}(s)}$ *) = dot g2 ekey.aw c_mid in
      let aw' (* $g_w^{\alpha_w (w_{mid}(s) + \delta_w t(s))}$ *) = G2.(aw + ekey.awt * dw) in

      (* $\alpha_y y_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_y y_k(s)$ *)
      let ay (* $g_y^{\alpha_y y_{mid}(s)}$ *) = dot g1 ekey.ay c_mid in
      let ay' (* $g_y^{\alpha_y (y_{mid}(s) + \delta_y t(s))}$ *) = G1.(ay + ekey.ayt * dy) in

      let bvwy (* $g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}$ *) =
        dot g1 ekey.bvwy c_mid
      in
      let bvwy' (* $g_v^{\beta (v_{mid}(s) + \delta_v t(s))} g_w^{\beta (w_{mid}(s) + \delta_w t(s))} g_y^{\beta (y_{mid}(s) + \delta_y t(s))}$ *) =
        G1.(bvwy + ekey.vbt * dv + ekey.wbt * dw + ekey.ybt * dy)
      in
      ignore v';
      ignore w';
      ignore y';
      ignore h';
      ignore av';
      ignore aw';
      ignore ay';
      ignore bvwy';
      { v = v;
        w = w;
        y = y;
        h = h;
        av = av;
        aw  = aw;
        ay = ay;
        bvwy = bvwy;
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
    x * x * x + x * Expr.int 2 + Expr.int 3
  in
  let rng = Random.State.make_self_init () in
  let prepare e =
    let circuit = Circuit.of_expr e in
    let qap, rk = QAP.build circuit.gates in
    prerr_endline "decompile";
    let gates = QAP.decompile qap rk in
    let gates : Circuit.Gate.t Var.Map.t =
      Var.Map.of_seq @@ List.to_seq @@
      List.map (fun (o,(l,r)) ->
          let f = List.map (fun (v, f) -> (v, Z.to_int @@ C.Fr.to_z f)) in
          o, (f l, f r)) gates
    in
    assert (Var.Map.equal (fun (l1, r1) (l2, r2) ->
        let l1 = List.sort compare l1 in
        let r1 = List.sort compare r1 in
        let l2 = List.sort compare l2 in
        let r2 = List.sort compare r2 in
        (l1, r1) = (l2, r2)) circuit.gates gates);
    circuit, qap
  in
  let circuit, qap = prepare e in
  let ekey, vkey = KeyGen.generate rng circuit qap in
  let proof =
    let sol = Result.get_ok @@ Circuit.eval [x, 10; Circuit.one, 1] circuit.gates in
    Format.(ef "@[<v>%a@]@." (list "@," (fun ppf (v,i) -> f ppf "%a = %d" Var.pp v i)) sol);
    let _p, h = QAP.eval sol qap in
    Compute.f ekey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq sol) h
  in
(*
  let _proof' =
    let sol = Result.get_ok @@ Circuit.eval [x, 11; Circuit.one, 1] circuit.gates in
    Format.(ef "@[<v>%a@]@." (list "@," (fun ppf (v,i) -> f ppf "%a = %d" Var.pp v i)) sol);
    let _p, h = QAP.eval sol qap in
    Compute.f ekey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq sol) h
  in
*)
  let () =
    let ios = Circuit.ios circuit in
    assert (Var.Set.equal ios (Var.Set.of_list [x; Circuit.one; Circuit.out]));
    let input = [x, 10; Circuit.one, 1] in
    let output = [Circuit.out, 1023] in
    Verify.f vkey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq (input @ output)) proof
  in

  prerr_endline "Veryfying with wrong out";
  let () =
    let ios = Circuit.ios circuit in
    assert (Var.Set.equal ios (Var.Set.of_list [x; Circuit.one; Circuit.out]));
    let input = [x, 10; Circuit.one, 1] in
    let output = [Circuit.out, 42] in
    try
      Verify.f vkey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq (input @ output)) proof;
      raise (Failure "Wot?")
    with
    | Assert_failure _ -> ()
  in

  prerr_endline "VC done!";

  let zcircuit = { circuit with mids = Var.Set.add x circuit.mids } in
  let ekey, vkey = KeyGen.generate rng zcircuit qap in
  let zkproof =
    let sol = Result.get_ok @@ Circuit.eval [x, 10; Circuit.one, 1] circuit.gates in
    let _p, h = QAP.eval sol qap in
    (* hide x *)
    ZKCompute.f rng qap.target ekey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq sol) h
  in
  let () =
    let ios = Circuit.ios zcircuit in
    assert (Var.Set.equal ios (Var.Set.of_list [Circuit.one; Circuit.out]));
    let input = [Circuit.one, 1] in
    let output = [Circuit.out, 1023] in
    Verify.f vkey (Var.Map.of_seq @@ Seq.map (fun (v,i) -> v, C.Fr.of_int i) @@ List.to_seq (input @ output)) zkproof
  in
  prerr_endline "PROTOCOL TEST done!"

let test () =
  let module QAPQ = QAP(Q) in
  QAPQ.test ();

  let module QAPBLS = QAP(Ecp.Bls12_381.Fr) in
  QAPBLS.test ();

  protocol_test ()
