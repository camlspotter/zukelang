(* This code implements Protocol 2 described in https://eprint.iacr.org/2013/279.pdf

   Protocol 1 is not for ordinary QAP.
*)

open Zukelang
open Var.Infix (* for (#!) *)
open Yojson_conv

module Make(C : Curve.S) = struct

  (* open, not include.
     [include C] instead opens the gate to the module typing hell *)
  open C

  module Poly    = Fr.Poly
  module Circuit = Circuit.Make(C.Fr)
  module QAP     = QAP.Make(C.Fr)

  type circuit = Circuit.t

  type qap = QAP.t

  module type G = Curve.G with type fr := Fr.t

  let g1 = (module G1 : G with type t = C.G1.t)
  let g2 = (module G2 : G with type t = C.G2.t)

  module KeyGen = struct

    (* Evaluation key in the paper.  We call it "proving key" *)
    (* The paper uses symmetric groups: e : $G_1 = G_2$.  Here we use BLS12-381
       with assymmetric groups $G_1 \neq G_2$.  Therefore some fields require values
       in $G_2$ too.

    *)
    type pkey =
      { vv    : G1.t Var.Map.t; (* $\{ g_v^{v_k(s)} \}_{k\in I_{mid}}$ *)
        ww    : G2.t Var.Map.t; (* $\{ g_w^{w_k(s)} \}_{k\in I_{mid}}$ *)
        yy    : G1.t Var.Map.t; (* $\{ g_y^{y_k(s)} \}_{k\in I_{mid}}$ *)
        vav   : G1.t Var.Map.t; (* $\{ g_v^{\alpha_v v_k(s)} \}_{k\in I_{mid}}$ *)
        waw   : G2.t Var.Map.t; (* $\{ g_w^{\alpha_w w_k(s)} \}_{k\in I_{mid}}$ *)
        yay   : G1.t Var.Map.t; (* $\{ g_y^{\alpha y_k(s)} \}_{k\in I_{mid}}$ *)
        si    : G1.t list; (* $\{ g_1^{s^i} \}_{i\in[d]}$ *)
        bvwy  : G1.t Var.Map.t; (* $\{ g_v^{\beta v_k(s)} g_w^{\beta w_k(s)} g_y^{\beta y_k(s)} \}_{k\in I_{mid}}$ *)

        (* Required for ZK *)
        si2   : G2.t list; (* $\{ g_1^{s^i} \}_{i\in[d]}$ *)
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
     } [@@deriving yojson]

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
      } [@@deriving yojson]

    let generate rng (circuit : Circuit.t) QAP.{v; w; y; target= t} =
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

      let b (* $\beta$ *)     = Fr.gen rng in
      let gm (* $\gamma$ *)   = Fr.gen rng in

      let ry (* $r_y$ *)      = Fr.(rv * rw) in

      let gv (* $g_v$ *)      = G1.of_Fr rv in
      let gw (* $g_w$ *)      = G1.of_Fr rw in
      let gw2                 = G2.of_Fr rw in
      let gy (* $g_y$ *)      = G1.of_Fr ry in
      let gy2                 = G2.of_Fr ry in

      let t = Poly.apply t s in

      (* $\{ g_u^{u_k(s)} \}_{k\in I_{set}}$ *)
      let map_apply_s (type t) (module G : G with type t = t) gu u set =
        Var.Map.of_set set @@ fun k ->
        let uk = u #! k in
        let uks = Poly.apply uk s in
        G.(gu * uks)
      in

      let pkey =
        (* $\{ g_v^{v_k(s)} \}_{k\in I_{mid}}$ *)
        let vv = map_apply_s g1 gv v imid in
        (* $\{ g_w^{w_k(s)} \}_{k\in I_{mid}}$ *)
        let ww1 = map_apply_s g1 gw w imid in
        let ww = map_apply_s g2 gw2 w imid in
        (* $\{ g_y^{y_k(s)} \}_{k\in I_{mid}}$ *)
        let yy = map_apply_s g1 gy y imid in

        (* $\{\alpha x_k\}_k$ *)
        let mul_map (type t) (module G : G with type t = t) m a =
          Var.Map.map (fun g -> G.(g * a)) m
        in

        (* $\{ g_v^{\alpha_v v_k(s)} \}_{k\in I_{mid}}$ *)
        let vav = mul_map g1 vv av in
        (* $\{ g_w^{\alpha_w w_k(s)} \}_{k\in I_{mid}}$ *)
        let waw = mul_map g2 ww aw in
        (* $\{ g_y^{\alpha_y y_k(s)} \}_{k\in I_{mid}}$ *)
        let yay = mul_map g1 yy ay in

        (* $\{ g^s^i \}_{i\in[d]}$ *)
        let si = G1.powers d s in
        let si2 = G2.powers d s in

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
        let v_all = map_apply_s g1 G1.one v m in

        (* $\{ g_1^{w_k(s)} \}_{k\in [m]$ *)
        let w_all = map_apply_s g1 G1.one w m in

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
        let vv_io (* $\{g_v^{v_k(s)}\}_{k\in [N]}$ *) = map_apply_s g1 gv v n in
        let ww_io (* $\{g_w^{w_k(s)}\}_{k\in [N]}$ *) = map_apply_s g2 gw2 w n in
        let yy_io (* $\{g_y^{y_k(s)}\}_{k\in [N]}$ *) = map_apply_s g1 gy y n in
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

      pkey, vkey

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
      } [@@deriving yojson]

    let f (pkey : KeyGen.pkey) (sol : Fr.t Var.Map.t) (h_poly : Poly.t) =
      let c = sol in
      let mid = Var.Map.domain pkey.vv in
      let c_mid = Var.Map.filter (fun v _ -> Var.Set.mem v mid) c in

      (* $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$ *)
      let vv (* $g_v^{v_{mid}(s)}$ *) = G1.dot pkey.vv c_mid in

      (* $w(s) = \Sigma_{k\in [m]} c_k \cdot w_k(s)$ *)
      let ww (* $g_w^{w_{mid}(s)}$ *) = G2.dot pkey.ww c_mid in

      (* $y(s) = \Sigma_{k\in [m]} c_k \cdot y_k(s)$ *)
      let yy (* $g_y^{y_{mid}(s)}$ *) = G1.dot pkey.yy c_mid in

      (* $h(s) = h_0 + h_1  s + h_2  s^2 + .. + h_d  s^d$ *)
      let h (* $g^{h(s)}$ *) = G1.apply_powers h_poly pkey.si in

      (* $\alpha_v v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_v v_k(s)$ *)
      let vavv (* $g_v^{\alpha v_{mid}(s)}$ *) = G1.dot pkey.vav c_mid in

      (* $\alpha_w w_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_w w_k(s)$ *)
      let waww (* $g_w^{\alpha_w w_{mid}(s)}$ *) = G2.dot pkey.waw c_mid in

      (* $\alpha_y y_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_y y_k(s)$ *)
      let yayy (* $g_y^{\alpha_y y_{mid}(s)}$ *) = G1.dot pkey.yay c_mid in

      let bvwy (* $g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}$ *) =
        G1.dot pkey.bvwy c_mid
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
        G1.sum_map c @@ fun k ck ->
            let vks = vkey.vv_io #! k in
            G1.(vks * ck)
      in

      let wio (* $g_w^{w_{io}(s)}$ *) =
        (* $g_w^{w_{io}(s)} = \Pi_{k\in [N]} (g_w^{w_k(s)})^{c_k} = \Pi_{k\in [N]} g_w^{w_k(s) \cdot c_k}$ *)
        assert (Var.Set.equal (Var.Map.domain c) (Var.Map.domain vkey.ww_io));
        G2.sum_map c @@ fun k ck ->
            let wks = vkey.ww_io #! k in
            G2.(wks * ck)
      in

      let yio (* $g_y^{y_{io}(s)}$ *) =
        (* $g_y^{y_{io}(s)} = \Pi_{k\in [N]} (g_y^{y_k(s)})^{c_k} = \Pi_{k\in [N]} g_y^{y_k(s) \cdot c_k}$ *)
        assert (Var.Set.equal (Var.Map.domain c) (Var.Map.domain vkey.yy_io));
        G1.sum_map c @@ fun k ck ->
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

    let f rng (target : Poly.t) (pkey : KeyGen.pkey) (sol : Fr.t Var.Map.t) (h_poly : Poly.t) =
      let dv (* $\delta_v$ *) = Fr.gen rng in
      let dw (* $\delta_w$ *) = Fr.gen rng in
      let dy (* $\delta_y$ *) = Fr.gen rng in
      let t (* $g_1^{t(s)}$, not $g_y^{t(s)}$! *) = G1.apply_powers target pkey.si in

      let c = sol in
      let mid = Var.Map.domain pkey.vv in
      let c_mid = Var.Map.filter (fun v _ -> Var.Set.mem v mid) c in

      (* $v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot v_k(s)$ *)
      let vv (* $g_v^{v_{mid}(s)}$ *) = G1.dot pkey.vv c_mid in
      let vv' (* $g_v^{v_{mid}(s) + \delta_v t(s)}$ *) = G1.(vv + pkey.vt * dv) in

      (* $w_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot w_k(s)$ *)
      let ww (* $g_w^{w_{mid}(s)}$ *) = G2.dot pkey.ww c_mid in
      let ww' (* $g_w^{w_{mid}(s) + \delta_w t(s)}$ *) = G2.(ww + pkey.wt * dw) in

      (* $y_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot y_k(s)$ *)
      let yy (* $g_y^{y_{mid}(s)}$ *) = G1.dot pkey.yy c_mid in
      let yy' (* $g_y^{y_{mid}(s) + \delta_y  t(s)}$ *) = G1.(yy + pkey.yt * dy) in

      (* $h(s) = h_0 + h_1  s + h_2  s^2 + .. + h_d  s^d$ *)
      let h (* $g^{h(s)}$ *) = G1.apply_powers h_poly pkey.si in
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
        let v_all (* $g_1^{v(s)}$ Not $g_v^{v(s)}$!! *) = G1.dot pkey.v_all c in
        let w_all (* $g_1^{w(s)}$ Not $g_w^{w(s)}$!! *) = G1.dot pkey.w_all c in
        h  +  v_all * dw  +  w_all * dv  +  t * dv * dw  -  one * dy
      in

      (* $\alpha_v v_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_v v_k(s)$ *)
      let vavv (* $g_v^{\alpha_v v_{mid}(s)}$ *) = G1.dot pkey.vav c_mid in
      let vavv' (* $g_v^{\alpha_v (v_{mid}(s) + \delta_v t(s))}$ *) = G1.(vavv + pkey.vavt * dv) in

      (* $\alpha_w w_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_w w_k(s)$ *)
      let waww (* $g_w^{\alpha_w w_{mid}(s)}$ *) = G2.dot pkey.waw c_mid in
      let waww' (* $g_w^{\alpha_w (w_{mid}(s) + \delta_w t(s))}$ *) = G2.(waww + pkey.wawt * dw) in

      (* $\alpha_y y_{mid}(s) = \Sigma_{k\in I_{mid}} c_k \cdot \alpha_y y_k(s)$ *)
      let yayy (* $g_y^{\alpha_y y_{mid}(s)}$ *) = G1.dot pkey.yay c_mid in
      let yayy' (* $g_y^{\alpha_y (y_{mid}(s) + \delta_y t(s))}$ *) = G1.(yayy + pkey.yayt * dy) in

      let bvwy (* $g_v^{\beta v_{mid}(s)} g_w^{\beta w_{mid}(s)} g_y^{\beta y_{mid}(s)}$ *) =
        G1.dot pkey.bvwy c_mid
      in
      let bvwy' (* $g_v^{\beta (v_{mid}(s) + \delta_v t(s))} g_w^{\beta (w_{mid}(s) + \delta_w t(s))} g_y^{\beta (y_{mid}(s) + \delta_y t(s))}$ *) =
        G1.(bvwy + pkey.vbt * dv + pkey.wbt * dw + pkey.ybt * dy)
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

  module NonZK = struct
    type f = C.Fr.t

    type nonrec circuit = circuit

    type nonrec qap = qap

    type pkey = KeyGen.pkey [@@deriving yojson]

    type vkey = KeyGen.vkey [@@deriving yojson]

    type proof = Compute.proof [@@deriving yojson]

    let keygen rng circuit qap =
      let pkey, vkey =
        KeyGen.generate rng circuit qap
      in
      pkey, vkey

    let prove _rng qap pkey sol =
      let _p, h = QAP.eval sol qap in
      Compute.f pkey sol h

    let verify input_output vkey proof =
      Verify.f vkey input_output proof
  end

  module ZK = struct
    type f = C.Fr.t

    type nonrec circuit = circuit

    type nonrec qap = qap

    type pkey = KeyGen.pkey [@@deriving yojson]

    type vkey = KeyGen.vkey [@@deriving yojson]

    type proof = Compute.proof [@@deriving yojson]

    let keygen = NonZK.keygen

    let prove rng qap pkey sol =
      let _p, h = QAP.eval sol qap in
      ZKCompute.f rng qap.target pkey sol h

    let verify = NonZK.verify
  end
end
