(* https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649 *)

open Utils
open Expr

module PQ = Polynomial.Make (Q)

let test () =
  let rhs =
    (* x^3 + x + 5 *)
    let open Expr in
    let open Expr.Infix in
    let x = var "x" in
    x * x * x + x + !!5
  in
  let open Format in
  (* x^3 + x + 5 = 35 when x = 3 *)
  assert (Expr.eval [(Var.of_string "x", 3)] rhs = 35) ;
  let lhs = Var.of_string "~out" in
  ef "%a = %a@." Var.pp lhs Expr.pp rhs ;

  prerr_endline "*** flatten" ;
  let fs = Flatten.flatten (lhs, rhs) in
  List.iter (fun eq -> ef "%a@." Flatten.pp eq) fs ;

  prerr_endline "*** solution vector" ;
  let sol = Flatten.eval [(Var.of_string "x", 3)] fs in
  let sol = (Var.of_string "~one", 1) :: sol in
  List.iter (fun (v, n) -> ef "%a : %d@." Var.pp v n) sol ;

  prerr_endline "*** R1CS elems" ;
  let vars = List.of_seq @@ Var.Set.to_seq @@ Flatten.vars fs in
  List.iter
    (fun f ->
      let res = R1CS.of_flatten vars f in
      ef "%a@." Flatten.pp f ;
      ef "%a@." R1CS.pp_elem res)
    fs ;

  prerr_endline "*** R1CS" ;
  let r1cs = R1CS.of_flatten_list vars fs in
  ef "%a@." R1CS.pp r1cs ;

  prerr_endline "*** check R1CS" ;
  R1CS.check r1cs sol ;

  prerr_endline "*** QAP" ;

  let module QAP = QAP.Make(Q) in

  let qabc = QAP.of_R1CS r1cs in
  ef "%a@." QAP.pp qabc;

  (* ABC.s *)
  let Abc.{ a= qas; b = qbs; c = qcs } = QAP.mul_sol qabc sol in
  ef "A.s = %a@." PQ.pp qas ;
  ef "B.s = %a@." PQ.pp qbs ;
  ef "C.s = %a@." PQ.pp qcs ;

  (* A.s * B.s - C.s *)
  let t = PQ.(add (mul qas qbs) (neg qcs)) in
  ef "T = A.s * B.s - C.s = %a@." PQ.pp t ;

  (* QAP check *)
  prerr_endline "*** QAP check" ;

  let q = Q.of_int in
  let z : PQ.t = PQ.z [q 1; q 2; q 3; q 4] in
  ef "Z = %a@." PQ.pp z ;
  let div, rem = PQ.div_rem t z in
  ef "H = T/Z = %a@." PQ.pp div ;
  ef "T mod Z = %a@." PQ.pp rem

(* Convert a circuit to QAP with Z *)
let qapinst sol (r1cs : R1CS.t) =
  let open Format in
  let open Ecp.Bls12_381 in
  (* let open Abc in *)
  prerr_endline "*** QAP";

  let module QAP_Q = QAP.Make(Q) in
  let qap = QAP_Q.of_R1CS r1cs in

  (* convert from Q to Fr *)
  let module QAP_Fr = QAP.Make(Fr) in
  let qap = QAP.conv Fr.of_q qap in
  ef "%a@." QAP_Fr.pp qap;

  (* A.s * B.s - C.s *)
  let abc_s = QAP_Fr.mul_sol qap sol in
  (* This t is called p in Pinoccio *)
  let t = Fr.Poly.(add (mul abc_s.a abc_s.b) (neg abc_s.c)) in
  ef "T = A.s * B.s - C.s = %a@." Fr.Poly.pp t ;

  let fr = Fr.of_int in
  (* This z is called t in Pinoccio.  How confusing! *)
  let z : Fr.Poly.t = Fr.Poly.z [fr 1; fr 2; fr 3; fr 4] in
  ef "Z = %a@." Fr.Poly.pp z;
  let div, rem = Fr.Poly.div_rem t z in
  ef "H = T/Z = %a@." Fr.Poly.pp div ;
  ef "T mod Z = %a@." Fr.Poly.pp rem ;

  (* A(x) * B(x) - C(x) = H(x) * Z(x) *)
  assert (Fr.Poly.normalize rem = Fr.Poly.zero) ;
  qap, z


let test2 () =
  let open Format in
  let rhs =
    (* x^3 + x + 5 *)
    let open Expr in
    let open Expr.Infix in
    let x = var "x" in
    x * x * x + x + !!5
  in
  (* x^3 + x + 5 = 35 when x = 3 *)
  assert (Expr.eval [(Var.of_string "x", 3)] rhs = 35) ;
  let lhs = Var.of_string "~out" in

  let fs = Flatten.flatten (lhs, rhs) in

  let sol = Flatten.eval [(Var.of_string "x", 3)] fs in
  let sol = (Var.of_string "~one", 1) :: sol in

  let vars = List.of_seq @@ Var.Set.to_seq @@ Flatten.vars fs in
  List.iter
    (fun f ->
      let res = R1CS.of_flatten vars f in
      ef "%a@." Flatten.pp f ;
      ef "%a@." R1CS.pp_elem res)
    fs ;

  let r1cs = R1CS.of_flatten_list vars fs in

  R1CS.check r1cs sol ;

  ignore @@ qapinst sol r1cs

(*
[@@@ocaml.warning "-26-27"]
let protocol2 rng qap sol _e =
  let open Ecp.Bls12_381 in
  let module QAP_Fr = QAP.Make(Fr) in

  let rhs =
    (* x^3 + x + 5 *)
    let open Expr in
    let open Expr.Infix in
    let x = var "x" in
    x * x * x + x + !!5
  in
  (* x^3 + x + 5 = 35 when x = 3 *)
  assert (Expr.eval [(Var.of_string "x", 3)] rhs = 35) ;
  let lhs = Var.of_string "~out" in
  let fs = Flatten.flatten (lhs, rhs) in
  let vars = List.of_seq @@ Var.Set.to_seq @@ Flatten.vars fs in
  let r1cs = R1CS.of_flatten_list vars fs in
  R1CS.check r1cs sol ;
  let qap = QAP_Fr.of_R1CS r1cs in
  let fr = Fr.of_int in
  let t : Fr.Poly.t = Fr.Poly.z [fr 1; fr 2; fr 3; fr 4] in

  let d (* degree *) = Fr.Poly.degree t in
  let m (* size *) = List.length qap.a in

  let mids, ios =
    let is_mid v =
      let n = Var.to_string v in
      n.[0] = '_'
    in
    List.partition is_mid @@ List.map fst qap.a
  in

  (* public evaluation key *)
  let module PEK = struct
    type t = { gv_vks : (Var.t * G1.t) list;
               gw_wks : (Var.t * G1.t) list;
               gy_yks : (Var.t * G1.t) list;
               gv_av_vks : (Var.t * G1.t) list;
               gw_aw_wks : (Var.t * G1.t) list;
               gy_ay_yks : (Var.t * G1.t) list;
               gsi : int -> G1.t;
               g_v_bvks_w_bwks_y_byks : (Var.t * G1.t) list }
  end in

  (* public verification key *)
  let module PVK = struct
    type t = { g_1 : G1.t;
               g_av : G1.t;
               g_aw : G1.t;
               g_ay : G1.t;
               g_g : G1.t;
               g_b_g : G1.t;
               gy_ts : G1.t;
               gv_vks : (Var.t * G1.t) list;
               gw_wks : (Var.t * G1.t) list;
               gy_yks : (Var.t * G1.t) list;  }
  end in

  let ekf, vkf =
    (* Choose rv,rw,s,αv,αw,αy,β,γ ←R F
       and set ry = rv ·rw,
               gv = g^{rv},
               gw = g^{rw}
           and gy = g^{ry}
    *)
    let rv = Fr.random ~state:rng () in
    let rw = Fr.random ~state:rng () in
    let s  = Fr.random ~state:rng () in
    let av = Fr.random ~state:rng () in
    let aw = Fr.random ~state:rng () in
    let ay = Fr.random ~state:rng () in
    let b  = Fr.random ~state:rng () in
    let g  = Fr.random ~state:rng () in
    let ry = Fr.(rv * rw) in
    let gv = G1.of_Fr rv in
    let gw = G1.of_Fr rw in
    let gy = G1.of_Fr ry in
    (* Construct the public evaluation key EKF as:
       ( {gv^{vk(s)}}k∈Imid ,
         {gw^{wk(s)}}k∈Imid ,
         {gy^{yk(s)}}k∈Imid ,

         {gv^{av * vk(s)}k∈Imid ,
         {gw^{aw * wk(s)}k∈Imid ,
         {gy^{ay * yk(s)}k∈Imid ,

         {g^s^i}i∈[d]

         {gv^{β * vk(s)},
         gw^{β * wk(s)},
         gy^{β * yk(s)}} k∈Imid
    *)
    let gx_xks gx x = (* g_v^{v_k(s)} *)
      List.map (fun k ->
          let xk : Fr.Poly.t = List.assoc k x in
          let xks = Fr.Poly.apply xk s in
          (k, G1.(gx * xks))) mids
    in
    let gv_vks = gx_xks gv qap.Abc.a in
    let gw_wks = gx_xks gw qap.Abc.b in
    let gy_yks = gx_xks gy qap.Abc.c in

    let gx_ax_xks gx ax x =
      List.map (fun k ->
          let xk : Fr.Poly.t = List.assoc k x in
          let xks = Fr.Poly.apply xk s in
          (k, G1.(gx * Fr.(ax * xks)))) mids
    in
    let gv_av_vks = gx_ax_xks gv av qap.Abc.a in
    let gw_aw_wks = gx_ax_xks gw aw qap.Abc.b in
    let gy_ay_yks = gx_ax_xks gy ay qap.Abc.c in

    let gsi i = G1.of_Fr Fr.(s ** Z.of_int i) in

    let g_v_bvks_w_bwks_y_byks =
      List.map (fun k ->
          let vk : Fr.Poly.t = List.assoc k qap.a in
          let vks = Fr.Poly.apply vk s in

          let wk : Fr.Poly.t = List.assoc k qap.a in
          let wks = Fr.Poly.apply wk s in

          let yk : Fr.Poly.t = List.assoc k qap.a in
          let yks = Fr.Poly.apply yk s in

          (* gv^(b*vk(s)) * gw^(b*wk(s)) * gy^(b*yk(s))
             = g^(rv*b*vk(s)) * g^(rw*b*wk(s)) * g^(ry*b*yk(s))
             = g^(rv*b*vk(s) + rw*b*wk(s) + ry*b*yk(s))
          *)
          (k, G1.of_Fr Fr.(rv * b * vks +  rw * b * wks + ry * b * yks))) mids
    in

    let ekf = PEK.{ gv_vks; gw_wks; gy_yks;
                    gv_av_vks; gw_aw_wks; gy_ay_yks;
                    gsi;
                    g_v_bvks_w_bwks_y_byks }
    in

    let g_1 = G1.one in
    let g_av = G1.of_Fr av in
    let g_aw = G1.of_Fr aw in
    let g_ay = G1.of_Fr ay in
    let g_g = G1.of_Fr g in
    let g_b_g = G1.of_Fr Fr.(b * g) in
    let gy_ts = G1.of_Fr Fr.(ry * Poly.apply t s) in

    (* for verification we list ios *)
    let gx_xks gx x =
      List.map (fun k ->
          let xk : Fr.Poly.t = List.assoc k x in
          let xks = Fr.Poly.apply xk s in
          (* gv^vk(s) = g^(rv * vk(s)) *)
          (k, G1.(gx * xks))) ios
    in
    let gv_vks = gx_xks gv qap.Abc.a in
    let gw_wks = gx_xks gw qap.Abc.b in
    let gy_yks = gx_xks gy qap.Abc.c in

    let vkf = PVK.{ g_1;
                    g_av;
                    g_aw;
                    g_ay;
                    g_g;
                    g_b_g;
                    gy_ts;
                    gv_vks;
                    gw_wks;
                    gy_yks }
    in
    ekf, vkf
  in

  let compute (ekf : PEK.t) expr u =
    let lhs = Var.of_string "~out" in
    let fs = Flatten.flatten (lhs, expr) in
    let sol (* circuit values *) = Flatten.eval u fs in

    let p : Fr.Poly.t =
      (* A.s * B.s - C.s *)
      let abc_s = QAP_Fr.mul_sol qap sol in
      Fr.Poly.(add (mul abc_s.a abc_s.b) (neg abc_s.c))
    in

    let h, rem = Fr.Poly.div_rem p t in
    assert (Fr.Poly.is_zero rem);

    (* proof *)
    let vmid x =
      let open Fr in
      sum
      @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let vk : Poly.t = List.assoc k qap.a in
          of_int ck * Poly.apply vk x) mids
    in
    let wmid x =
      let open Fr in
      sum
      @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let wk : Poly.t = List.assoc k qap.b in
          of_int ck * Poly.apply wk x) mids
    in
    let ymid x =
      let open Fr in
      sum
      @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let yk : Poly.t = List.assoc k qap.c in
          of_int ck * Poly.apply yk x) mids
    in
    let gv_vmids =
      (* vmid(x) = ∑k∈Imid ck · vk(x)
         gv^vmid(s) = gv^(ck0*vk0(s) + .. + ckn*vkn(s))
                    = gv^(ck0*vk0(s)) * .. * gv^(ckn*vkn(s))
                    = gv^vk0(s) * ck0 + .. + gv^vkn(s) * ckn
      *)

      let open G1 in
      sum @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let gv_vks = List.assoc k ekf.gv_vks in
          gv_vks * Fr.of_int ck) mids
    in
    let gw_wmids =
      let open G1 in
      sum @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let gw_wks = List.assoc k ekf.gw_wks in
          gw_wks * Fr.of_int ck) mids
    in
    let gy_ymids =
      let open G1 in
      sum @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let gy_yks = List.assoc k ekf.gy_yks in
          gy_yks * Fr.of_int ck) mids
    in
    let g_hs =
      G1.sum @@
      List.mapi (fun i c -> G1.(ekf.gsi i * c)) h
    in
    let gv_av_vmids =
      (* vmid(x) = ∑k∈Imid ck · vk(x)
         gv^(av * vmid(s)) = gv^(av*ck0*vk0(s) + .. + av*ckn*vkn(s))
                            = gv^(av*ck0*vk0(s)) * .. * gv^(av*ckn*vkn(s))
                            = gv^(av * vk0(s)) * ck0 + .. + gv^(av * vkn(s)) * ckn
      *)
      let open G1 in
      sum @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let gv_av_vks = List.assoc k ekf.gv_av_vks in
          gv_av_vks * Fr.of_int ck) mids
    in
    let gw_aw_wmids =
      let open G1 in
      sum @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let gw_aw_wks = List.assoc k ekf.gw_aw_wks in
          gw_aw_wks * Fr.of_int ck) mids
    in
    let gy_ay_ymids =
      let open G1 in
      sum @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let gy_ay_yks = List.assoc k ekf.gy_ay_yks in
          gy_ay_yks * Fr.of_int ck) mids
    in

    let g_v_b_vmids_w_b_wmids_y_b_ymids =
      (* vmid(x) = ∑k∈Imid ck · vk(x)
         gv^(b * vmid(s)) = gv^(b*ck0*vk0(s) + .. + b*ckn*vkn(s))
                          = gv^(b*ck0*vk0(s)) * .. * gv^(b*ckn*vkn(s))
                          = gv^(b * vk0(s)) * ck0 + .. + gv^(b * vkn(s)) * ckn

         gw^(b * wmid(s)) = gw^(b*ck0*wk0(s) + .. + b*ckn*wkn(s))
                          = gw^(b*ck0*wk0(s)) * .. * gw^(b*ckn*wkn(s))
                          = gw^(b * wk0(s)) * ck0 + .. + gw^(b * wkn(s)) * ckn

         gy^(b * ymid(s)) = gy^(b*ck0*yk0(s) + .. + b*ckn*ykn(s))
                          = gy^(b*ck0*yk0(s)) * .. * gy^(b*ckn*ykn(s))
                          = gy^(b * yk0(s)) * ck0 + .. + gy^(b * ykn(s)) * ckn
      *)
      let open G1 in
      sum @@ List.map (fun k ->
          let ck = List.assoc k sol in
          let g_v_bvks_w_bwks_y_byks = List.assoc k ekf.g_v_bvks_w_bwks_y_byks in
          g_v_bvks_w_bwks_y_byks * Fr.of_int ck) mids
    in
    ( gv_vmids, gw_wmids, gy_ymids, g_hs,
      gv_av_vmids, gw_aw_wmids, gy_ay_ymids,
      g_v_b_vmids_w_b_wmids_y_b_ymids )
  in

  let verify (vkf : PVK.t) u y
      (g_vmid, g_wmid, g_ymid, g_h, g_v'mid, g_w'mid, g_y'mid, g_z)
    =
    let gv_vios =
      (*  ∏k∈[N] (gv_vks)^ck) *)
      G1.sum @@
      List.map (fun k ->
          let ck = List.assoc k sol in
          let gv_vks = List.assoc k vkf.gv_vks in
          G1.(gv_vks * Fr.of_int ck)) ios
    in
    let gw_wios =
      G1.sum @@
      List.map (fun k ->
          let ck = List.assoc k sol in
          let gw_wks = List.assoc k vkf.gw_wks in
          G1.(gw_wks * Fr.of_int ck)) ios
    in
    let gy_yios =
      G1.sum @@
      List.map (fun k ->
          let ck = List.assoc k sol in
          let gy_yks = List.assoc k vkf.gy_yks in
          G1.(gy_yks * Fr.of_int ck)) ios
    in
    (* e (gv_v0s * gv_vios * gv_vmid, gw_w0s * gw_wios * gw_wmid)
       = e (gy_ts, g_h) * e (gy_y0s * gy_yios * gy_ymid, g1)
    *)
  in
  assert false
                             *)
