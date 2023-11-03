(* This code implements Protocol 2 described in https://eprint.iacr.org/2013/279.pdf

   Protocol 1 is not for ordinary QAP.
*)

open Utils
open Var.Infix (* for (#!) *)

module type CURVE = sig
  module Fr : sig
    include Field.S
    val ( ** ) : t -> Z.t -> t
    val gen : t Gen.t
  end
  module G1 : Ecp.G with type fr := Fr.t
  module G2 : Ecp.G with type fr := Fr.t
  module GT : Ecp.G with type fr := Fr.t
  module Pairing : sig
    val pairing : G1.t -> G2.t -> GT.t
  end
end

module Make(C : CURVE) = struct

  (* open, not include.
     [include C] instead opens the gate to the module typing hell *)
  open C

  module Polynomial = Polynomial.Make(C.Fr)
  module Lang = Lang.Make(C.Fr)
  module Circuit = Circuit.Make(C.Fr)
  module QAP = QAP.Make(C.Fr)

  type expr = Lang.Expr.t

  type circuit = Circuit.t

  type qap = QAP.t

  module type G = Ecp.G with type fr := Fr.t

  let g1 = (module G1 : G with type t = C.G1.t)
  let g2 = (module G2 : G with type t = C.G2.t)

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
  let apply_powers (type t) (module G : G with type t = t) (cs : Polynomial.t)  xis =
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
      { vv    : G1.t Var.Map.t; (* $\{ g_v^{v_k(s)} \}_{k\in I_{mid}}$ *)
        ww    : G2.t Var.Map.t; (* $\{ g_w^{w_k(s)} \}_{k\in I_{mid}}$ *)
        yy    : G1.t Var.Map.t; (* $\{ g_y^{y_k(s)} \}_{k\in I_{mid}}$ *)
        vav   : G1.t Var.Map.t; (* $\{ g_v^{\alpha_v v_k(s)} \}_{k\in I_{mid}}$ *)
        waw   : G2.t Var.Map.t; (* $\{ g_w^{\alpha_w w_k(s)} \}_{k\in I_{mid}}$ *)
        yay   : G1.t Var.Map.t; (* $\{ g_y^{\alpha y_k(s)} \}_{k\in I_{mid}}$ *)
        si    : (int * G1.t) list; (* $\{ g_1^{s^i} \}_{i\in[d]}$ *)
        bvwy  : G1.t Var.Map.t; (* $\{ g_v^{\beta v_k(s)} g_w^{\beta w_k(s)} g_y^{\beta y_k(s)} \}_{k\in I_{mid}}$ *)

        (* Required for ZK *)
        si2   : (int * G2.t) list; (* $\{ g_1^{s^i} \}_{i\in[d]}$ *)
        vt    : G1.t; (* $g_v^{t(s)}$ *)
        wt    : G2.t; (* $g_w^{t(s)}$ *)
        yt    : G1.t; (* $g_y^{t(s)}$ *)
        vavt  : G1.t; (* $g_v^{\alpha_v t(s)}$ *)
        wawt  : G2.t; (* $g_w^{\alpha_y t(s)}$ *)
        yayt  : G1.t; (* $g_y^{\alpha_w t(s)}$ *)
        vbt   : G1.t;  (* $g_v^{\beta t(s)}$ *)
        wbt   : G1.t;  (* $g_w^{\beta t(s)}$ *)
        ybt   : G1.t;  (* $g_y^{\beta t(s)}$ *)
        v_all : G1.t Var.Map.t; (* $\{ g_1^{v_k(s)} \}_{k\in [m]}$ Not $g_v^{v_k(s)}$!! *)
        w_all : G1.t Var.Map.t; (* $\{ g_1^{w_k(s)} \}_{k\in [m]$ Not $g_w^{v_k(s)}$!! *)
     }

    type vkey =
      { one    : G1.t; (* $g^1$ *)
        one2   : G2.t; (* $g^1$ *)
        av     : G2.t; (* $g^{\alpha_v}$ *)
        aw     : G1.t; (* $g^{\alpha_w}$ *)
        ay     : G2.t; (* $g^{\alpha_y}$ *)
        gm2    : G2.t; (* $g^\gamma$ *)
        bgm    : G1.t; (* $g^{\beta\gamma}$ *)
        bgm2   : G2.t; (* $g^{\beta\gamma}$ *)
        yt     : G2.t; (* $g_y^{t(s)}$ *)
        vv_io : G1.t Var.Map.t; (* $\{ g_v^{v_k(s)} \}_{k\in [N]}$ *)
        ww_io : G2.t Var.Map.t; (* $\{ g_w^{w_k(s)} \}_{k\in [N]}$ *)
        yy_io : G1.t Var.Map.t; (* $\{ g_y^{y_k(s)} \}_{k\in [N]}$ *)
      }

    let generate rng (circuit : Circuit.t) QAP.{vwy; target= t} =
      let imid (* $I_{mid}$ *) = circuit.mids in
      let n (* $[N]$ *) = Circuit.ios circuit in
      let m (* [m] *) = Circuit.vars circuit.gates in
      let d = Polynomial.degree t in

      let rv (* $r_v$ *)      = Fr.gen rng in
      let rw (* $r_w$ *)      = Fr.gen rng in
      let s (* $s$ *)         = Fr.gen rng in
      let av (* $\alpha_v$ *) = Fr.gen rng in
      let aw (* $\alpha_w$ *) = Fr.gen rng in
      let ay (* $\alpha_y$ *) = Fr.gen rng in

      let b (* $\beta$ *)     = Fr.gen rng in
      let gm (* $\gamma$ *)   = Fr.gen rng in

      let ry (* $r_y$ *)      = Fr.(rv * rw) in

      let gv (* $g_v$ *)      = G1.of_Fr rv in
      let gw (* $g_w$ *)      = G1.of_Fr rw in
      let gw2                 = G2.of_Fr rw in
      let gy (* $g_y$ *)      = G1.of_Fr ry in
      let gy2                 = G2.of_Fr ry in

      let t = Polynomial.apply t s in

      (* $\{ g_u^{u_k(s)} \}_{k\in I_{set}}$ *)
      let map_apply_s (type t) (module G : G with type t = t) gu u set =
        Var.Map.of_set set @@ fun k ->
        let uk = u #! k in
        let uks = Polynomial.apply uk s in
        G.(gu * uks)
      in

      let ekey =
        (* $\{ g_v^{v_k(s)} \}_{k\in I_{mid}}$ *)
        let vv = map_apply_s g1 gv vwy.v imid in
        (* $\{ g_w^{w_k(s)} \}_{k\in I_{mid}}$ *)
        let ww1 = map_apply_s g1 gw vwy.w imid in
        let ww = map_apply_s g2 gw2 vwy.w imid in
        (* $\{ g_y^{y_k(s)} \}_{k\in I_{mid}}$ *)
        let yy = map_apply_s g1 gy vwy.y imid in

        (* $\{ g_v^{\alpha_v v_k(s)} \}_{k\in I_{mid}}$ *)
        let vav = mul_map g1 vv av in
        (* $\{ g_w^{\alpha_w w_k(s)} \}_{k\in I_{mid}}$ *)
        let waw = mul_map g2 ww aw in
        (* $\{ g_y^{\alpha_y y_k(s)} \}_{k\in I_{mid}}$ *)
        let yay = mul_map g1 yy ay in

        (* $\{ g^s^i \}_{i\in[d]}$ *)
        let si = powers g1 d s in
        let si2 = powers g2 d s in

        (* $\{ g_v^{\beta v_k(s)} g_w^{\beta w_k(s)} g_y^{\beta y_k(s)} \}_{k\in I_{mid}}$ *)
        let bvwy =
          Var.Map.of_set imid @@ fun k ->
          G1.( ((vv #! k) + (ww1 #! k) + (yy #! k)) * b )
        in

        let vt (* $g_v^{t(s)}$ *) = G1.(gv * t) in
        let wt (* $g_w^{t(s)}$ *) = G2.(gw2 * t) in
        let yt (* $g_y^{t(s)}$ *) = G1.(gy * t) in
        let vavt (* $g_v^{\alpha_v t(s)}$ *) = G1.(gv * av * t) in
        let wawt (* $g_w^{\alpha_w t(s)}$ *) = G2.(gw2 * aw * t) in
        let yayt (* $g_y^{\alpha_y t(s)}$ *) = G1.(gy * ay * t) in
        let vbt (* $g_v^{\beta t(s)}$ *) = G1.(gv * b * t) in
        let wbt (* $g_w^{\beta t(s)}$ *) = G1.(gw * b * t) in
        let ybt (* $g_y^{\beta t(s)}$ *) = G1.(gy * b * t) in

        (* $\{ g_1^{v_k(s)} \}_{k\in [m]$ *)
        let v_all = map_apply_s g1 G1.one vwy.v m in

        (* $\{ g_1^{w_k(s)} \}_{k\in [m]$ *)
        let w_all = map_apply_s g1 G1.one vwy.w m in

        { vv; ww; yy; vav; waw; yay; si; bvwy;
          si2; vt; wt; yt; vavt; wawt; yayt; vbt; wbt; ybt; v_all; w_all }
      in

      let vkey =
        let one (* $g^1$ *) = G1.one in
        let one2 (* $g^1$ *) = G2.one in
        let av (* $g^{\alpha_v}$ *) = G2.of_Fr av in
        let aw (* $g^{\alpha_w}$ *) = G1.of_Fr aw in
        let ay (* $g^{\alpha_y}$ *) = G2.of_Fr ay in
        let gm, gm2 (* $g^\gamma$ *) = G1.of_Fr gm, G2.of_Fr gm in
        let bgm (* $g^{\beta\gamma}$ *) = G1.(gm * b) in
        let bgm2 (* $g^{\beta\gamma}$ *) = G2.(gm2 * b) in
        let yt (* $g_y^{t(s)}$ *) = G2.(gy2 * t) in
        let vv_io (* $\{g_v^{v_k(s)}\}_{k\in [N]}$ *) = map_apply_s g1 gv vwy.v n in
        let ww_io (* $\{g_w^{w_k(s)}\}_{k\in [N]}$ *) = map_apply_s g2 gw2 vwy.w n in
        let yy_io (* $\{g_y^{y_k(s)}\}_{k\in [N]}$ *) = map_apply_s g1 gy vwy.y n in
        { one;
          one2;
          av;
          aw;
          ay;
          gm2;
          bgm;
          bgm2;
          yt;
          vv_io;
          ww_io;
          yy_io; }
      in

      ekey, vkey

  end

  module Compute = struct

    type proof =
      { vv  : G1.t; (* $g_v^{v_{mid}(s)}$ *)
        ww  : G2.t; (* $g_w^{w_{mid}(s)}$ *)
        yy  : G1.t; (* $g_y^{y_{mid}(s)}$ *)

        h  : G1.t;  (* $g^{h(s)}$ *)

        vavv : G1.t; (* $g_v^{\alpha_v v_{mid}(s)}$ *)

        waww : G2.t; (* $g_w^{\alpha_w w_{mid}(s)}$ *)
        yayy : G1.t; (* $g_y^{\alpha_y y_{mid}(s)}$ *)

        bvwy : G1.t; (* $g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}$ *)
      }

    let f (ekey : KeyGen.ekey) (sol : Fr.t Var.Map.t) (h_poly : Polynomial.t) =
      let c = sol in
      let mid = Var.Map.domain ekey.vv in
      let c_mid = Var.Map.filter (fun v _ -> Var.Set.mem v mid) c in

      (* $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$ *)
      let vv (* $g_v^{v_{mid}(s)}$ *) = dot g1 ekey.vv c_mid in

      (* $w(s) = \Sigma_{k\in [m]} c_k \cdot w_k(s)$ *)
      let ww (* $g_w^{w_{mid}(s)}$ *) = dot g2 ekey.ww c_mid in

      (* $y(s) = \Sigma_{k\in [m]} c_k \cdot y_k(s)$ *)
      let yy (* $g_y^{y_{mid}(s)}$ *) = dot g1 ekey.yy c_mid in

      (* $h(s) = h_0 + h_1  s + h_2  s^2 + .. + h_d  s^d$ *)
      let h (* $g^{h(s)}$ *) = apply_powers g1 h_poly ekey.si in

      (* $\alpha_v v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_v v_k(s)$ *)
      let vavv (* $g_v^{\alpha v_{mid}(s)}$ *) = dot g1 ekey.vav c_mid in

      (* $\alpha_w w_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_w w_k(s)$ *)
      let waww (* $g_w^{\alpha_w w_{mid}(s)}$ *) = dot g2 ekey.waw c_mid in

      (* $\alpha_y y_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_y y_k(s)$ *)
      let yayy (* $g_y^{\alpha_y y_{mid}(s)}$ *) = dot g1 ekey.yay c_mid in

      let bvwy (* $g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}$ *) =
        dot g1 ekey.bvwy c_mid
      in

      { vv;
        ww;
        yy;
        h;
        vavv;
        waww;
        yayy;
        bvwy;
      }

  end

  module Verify = struct

    let f (vkey : KeyGen.vkey) (ios : Fr.t Var.Map.t) (proof : Compute.proof) =
      let c = ios in (* $Dom(c) = [N]$ *)

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

         In the public information, the things multiplied by $\alpha_v$ are:
           - $\{\alpha_v r_v v_k(s)\}$
           - $\alpha_v r_v t(s)$
         Since $t(s)$ is not public, the verifier can confirm that proof.vv
         must be derived only from $r_v v_k(s)$.
      *)
      assert (e proof.vv vkey.av = e proof.vavv vkey.one2);

      (* KC check
         $w(s)$ is really a linear combination of $\{w_k(s)\}$.
         Actually, $w(s) = \Sigma_{k\in I_{mid}} c_k \cdot w_k(s)$
         $e(g^{\alpha_w}, g_w^{w_{mid}(s)}) = e(g, g_w^{\alpha_w w_{mid}(s)})$

         In the public information, the things multiplied by $\alpha_w$ are:
           - $\{\alpha_w r_w w_k(s)\}$
           - $\alpha_w r_w t(s)$
         Since $t(s)$ is not public, the verifier can confirm that proof.ww
         must be derived only from $r_w w_k(s)$.
      *)
      assert (e vkey.aw proof.ww = e vkey.one proof.waww);

      (* KC check
         $y(s)$ is really a linear combination of $\{y_k(s)\}$.
         Actually, $y(s) = \Sigma_{k\in I_{mid}} c_k \cdot y_k(s)$
         $e(g_y^{y_{mid}(s)}, g^{\alpha_y}) = e(g_y^{\alpha_y y_{mid}(s)}, g)$

         In the public information, the things multiplied by $\alpha_y$ are:
           - $\{\alpha_y r_y y_k(s)\}$
           - $\alpha_y r_y t(s)$
         Since $t(s)$ is not public, the verifier can confirm that proof.yy
         must be derived only from $r_y y_k(s)$.
      *)
      assert (e proof.yy vkey.ay = e proof.yayy vkey.one2);

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

         The above 3 KC checks for proof.vv, proof.ww, and proof.yy tell that
         they are linear combinations of $\{*_k(s)\}$ with some sets of coefficients.

         Now here we are going to prove that they are linear combinations of
         the same coefficients.

         If the test passes we have:

            $\gamma{\tt proof.rvwk} = \gamma\beta({\tt vv} + {\tt ww} + {\tt yy})$

         for some secret $\beta$ and $\gamma$.

         Since $\beta$ is secret, only way for the prover to create a multiplication
         of $\beta$ is to use the public values multiplied by $\beta$:

           - $\{ \beta (r_v v_k(s) + r_w w_k(s) + r_y y_k(s)) \}_{k\in I_{mid}}$
           - $\beta r_v t(s)$, $\beta r_w t(s)$, $\beta r_y t(s)$

         For the RHS, the previous 3 KC checks shown that
           - vv is a linear combination of $\{r_v v_k(s)\}$
           - ww is a linear combination of $\{r_w w_k(s)\}$
           - yy is a linear combination of $\{r_y y_k(s)\}$

         Now we have

         $\beta \{c_k\}\{ r_v v_k(s) + r_w w_k(s) + r_y y_k(s) \}
          + \beta ( c_1 r_v + c_2 r_w + c_3 r_y ) t(s)$
          $= c_v \{r_v v_k(s)\}
          + c_w \{r_v v_k(s)\}
          + c_y \{r_v v_k(s)\}$

         Since $r_vv_k(s)$, $r_ww_k(s)$, $r_yy_k(s)$, $t(s)$ are unrelated, the only possible way
         to make this equation hold is $c_k = c_v = c_w = c_y$ and $c_1r_v + c_wr_w + c_3r_y = 0$.
      *)
      assert (
          e proof.bvwy vkey.gm2
          = e proof.vv vkey.bgm2
            + e vkey.bgm proof.ww
            + e proof.yy vkey.bgm2
        );

      let vio (* $g_v^{v_{io}(s)}$ *) =
        (* $g_v^{v_{io}(s)} = \Pi_{k\in [N]} (g_v^{v_k(s)})^{c_k} = \Pi_{k\in [N]} g_v^{v_k(s) \cdot c_k}$
           The paper uses prod for the operaiton of Gi.  Our code uses add instead *)
        assert (Var.Set.equal (Var.Map.domain c) (Var.Map.domain vkey.vv_io));
        sum_map g1 c @@ fun k ck ->
            let vks = vkey.vv_io #! k in
            G1.(vks * ck)
      in

      let wio (* $g_w^{w_{io}(s)}$ *) =
        (* $g_w^{w_{io}(s)} = \Pi_{k\in [N]} (g_w^{w_k(s)})^{c_k} = \Pi_{k\in [N]} g_w^{w_k(s) \cdot c_k}$ *)
        assert (Var.Set.equal (Var.Map.domain c) (Var.Map.domain vkey.ww_io));
        sum_map g2 c @@ fun k ck ->
            let wks = vkey.ww_io #! k in
            G2.(wks * ck)
      in

      let yio (* $g_y^{y_{io}(s)}$ *) =
        (* $g_y^{y_{io}(s)} = \Pi_{k\in [N]} (g_y^{y_k(s)})^{c_k} = \Pi_{k\in [N]} g_y^{y_k(s) \cdot c_k}$ *)
        assert (Var.Set.equal (Var.Map.domain c) (Var.Map.domain vkey.yy_io));
        sum_map g1 c @@ fun k ck ->
            let yks = vkey.yy_io #! k in
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
      e G1.(vio + proof.vv) G2.(wio + proof.ww)
      - e G1.(yio + proof.yy) vkey.one2
      = e proof.h vkey.yt
  end

  module ZKCompute = struct

    open Compute

    let f rng (target : Polynomial.t) (ekey : KeyGen.ekey) (sol : Fr.t Var.Map.t) (h_poly : Polynomial.t) =
      let dv (* $\delta_v$ *) = Fr.gen rng in
      let dw (* $\delta_w$ *) = Fr.gen rng in
      let dy (* $\delta_y$ *) = Fr.gen rng in
      let t (* $g_1^{t(s)}$, not $g_y^{t(s)}$! *) = apply_powers g1 target ekey.si in

      let c = sol in
      let mid = Var.Map.domain ekey.vv in
      let c_mid = Var.Map.filter (fun v _ -> Var.Set.mem v mid) c in

      (* $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$ *)
      let vv (* $g_v^{v_{mid}(s)}$ *) = dot g1 ekey.vv c_mid in
      let vv' (* $g_v^{v_{mid}(s) + \delta_v t(s)}$ *) = G1.(vv + ekey.vt * dv) in

      (* $w_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot w_k(s)$ *)
      let ww (* $g_w^{w_{mid}(s)}$ *) = dot g2 ekey.ww c_mid in
      let ww' (* $g_w^{w_{mid}(s) + \delta_w t(s)}$ *) = G2.(ww + ekey.wt * dw) in

      (* $y_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot y_k(s)$ *)
      let yy (* $g_y^{y_{mid}(s)}$ *) = dot g1 ekey.yy c_mid in
      let yy' (* $g_y^{y_{mid}(s) + \delta_y  t(s)}$ *) = G1.(yy + ekey.yt * dy) in

      (* $h(s) = h_0 + h_1  s + h_2  s^2 + .. + h_d  s^d$ *)
      let h (* $g^{h(s)}$ *) = apply_powers g1 h_poly ekey.si in
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
      let vavv (* $g_v^{\alpha_v v_{mid}(s)}$ *) = dot g1 ekey.vav c_mid in
      let vavv' (* $g_v^{\alpha_v (v_{mid}(s) + \delta_v t(s))}$ *) = G1.(vavv + ekey.vavt * dv) in

      (* $\alpha_w w_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_w w_k(s)$ *)
      let waww (* $g_w^{\alpha_w w_{mid}(s)}$ *) = dot g2 ekey.waw c_mid in
      let waww' (* $g_w^{\alpha_w (w_{mid}(s) + \delta_w t(s))}$ *) = G2.(waww + ekey.wawt * dw) in

      (* $\alpha_y y_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_y y_k(s)$ *)
      let yayy (* $g_y^{\alpha_y y_{mid}(s)}$ *) = dot g1 ekey.yay c_mid in
      let yayy' (* $g_y^{\alpha_y (y_{mid}(s) + \delta_y t(s))}$ *) = G1.(yayy + ekey.yayt * dy) in

      let bvwy (* $g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}$ *) =
        dot g1 ekey.bvwy c_mid
      in
      let bvwy' (* $g_v^{\beta (v_{mid}(s) + \delta_v t(s))} g_w^{\beta (w_{mid}(s) + \delta_w t(s))} g_y^{\beta (y_{mid}(s) + \delta_y t(s))}$ *) =
        G1.(bvwy + ekey.vbt * dv + ekey.wbt * dw + ekey.ybt * dy)
      in
      { vv = vv';
        ww = ww';
        yy = yy';
        h = h';
        vavv = vavv';
        waww  = waww';
        yayy = yayy';
        bvwy = bvwy';
      }
  end

  module API = struct

    type ekey = KeyGen.ekey

    type vkey = KeyGen.vkey

    type proof = Compute.proof

    let compile e =
      let circuit = Circuit.of_expr e in
      let qap, rk = QAP.build circuit.gates in

      (* decompilation test *)
      let gates = QAP.decompile qap rk in
      assert (Circuit.equal_gates circuit.gates gates);

      circuit, qap

    let keygen circuit qap =
      let ekey, vkey =
        let rng = Random.State.make_self_init () in
        KeyGen.generate rng circuit qap
      in
      ekey, vkey

    let solve (circuit : Circuit.t) input =
      let input = Var.Map.add Circuit.one (Fr.of_int 1) input in
      Result.get_ok @@ Circuit.eval input circuit.gates

    let output_of_solution (circuit : Circuit.t) sol =
      Var.Map.filter (fun v _ -> Var.Set.mem v circuit.output) sol

    let prove qap ekey sol =
      let _p, h = QAP.eval sol qap in
      Compute.f ekey sol h

    let verify input_output vkey proof =
      let input_output = Var.Map.add Circuit.one (Fr.of_int 1) input_output in
      Verify.f vkey input_output proof

    let zkkeygen (circuit : Circuit.t) qap secret_input =
      let circuit =
        { circuit
          with mids = Var.Set.union circuit.mids secret_input }
      in
      keygen circuit qap

    let zkprove qap ekey sol =
      let rng = Random.State.make_self_init () in
      let _p, h = QAP.eval sol qap in
      ZKCompute.f rng qap.target ekey sol h
  end

  include API
end

let test () =
  prerr_endline "PROTOCOL TEST";

  let module C = Ecp.Bls12_381 in
  let module Fr = C.Fr in
  let module Lang = Lang.Make(Fr) in
  let module P = Make(C) in
  let open P in

  let x = Var.of_string "i" in
  let e =
    let open Lang in
    let open Expr.Infix in
    let x = Expr.Term (Var x) in
    x * x * x + x * !!!2 + !!!3
  in

  (* VC *)

  let circuit, qap = API.compile e in

  let ekey, vkey = API.keygen circuit qap in

  let input = Var.Map.of_list [x, Fr.of_int 10] in

  let sol = API.solve circuit input in

  let output = API.output_of_solution circuit sol in

  let proof = API.prove qap ekey sol in

  assert (API.verify (Var.Map.concat input output) vkey proof);

  let wrong_output = Var.Map.singleton Circuit.out (Fr.of_int 42) in
  assert (not @@ API.verify (Var.Map.concat input wrong_output) vkey proof);

  (* VC with ZK *)

  let ekey, vkey = API.zkkeygen circuit qap (Var.Set.singleton x) in

  let proof = API.zkprove qap ekey sol in

  assert (API.verify output vkey proof);
  assert (not @@ API.verify wrong_output vkey proof);

  (* VC using ZK version *)

  let ekey, vkey = API.zkkeygen circuit qap Var.Set.empty in

  let proof = API.zkprove qap ekey sol in

  assert (API.verify (Var.Map.concat input output) vkey proof);
  assert (not @@ API.verify (Var.Map.concat input wrong_output) vkey proof);

  prerr_endline "Pinocchio test done!"
