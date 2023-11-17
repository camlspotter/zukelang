open Misc

open Var.Infix

type 'a vwy = { v : 'a; w : 'a; y : 'a }

module Make(F : Field.S) = struct

  type nonrec 'a vwy = 'a vwy = { v : 'a; w : 'a; y : 'a }

  module Polynomial = Polynomial.Make(F)
  module Lang = Lang.Make(F)
  module Circuit = Circuit.Make(F)

  type t =
    { vwy : Polynomial.t Var.Map.t vwy;
      target : Polynomial.t
    }

  let build (gates : Circuit.Gate.t Var.Map.t) =
    let rk =
      List.mapi (fun i (v, _) ->
          Format.eprintf "gate %a : r_%a = %d@."
            Var.pp v Var.pp v i;
          v, F.of_int i) @@ Var.Map.bindings gates in
    let vars = Circuit.vars gates in

    let make_matrix f =
      Var.Map.of_set vars @@ fun k -> Var.Map.mapi (f k) gates
    in

    let v =
      (* $v_k(r_g) = 1$ when gate $g$ has $c_k$ at the left of op *)
      make_matrix @@ fun k _g (l, _r) ->
      match Var.Map.find_opt k l with
      | None -> F.zero
      | Some n -> n
    in

    let w =
      (* $w_k(r_g) = 1$ when gate $g$ has $c_k$ at the right of op *)
      make_matrix @@ fun k _g (_l, r) ->
      match Var.Map.find_opt k r with
      | None -> F.zero
      | Some n -> n
    in

    let y =
      (* $y_k(r_g) = 1$ when gate (v, _, _) , $v = c_k$ *)
      make_matrix @@ fun k g (_l, _r) ->
      if k = g then F.one else F.zero
    in

    Var.Map.iter (fun k gns ->
        Var.Map.iter (fun g n ->
            Format.ef "v_%a(r_%a) = %a # gate %a has %a in the left arg@."
              Var.pp k
              Var.pp g
              F.pp n
              Var.pp g
              Var.pp k) gns) v;
    Var.Map.iter (fun k gns ->
        Var.Map.iter (fun g n ->
            Format.ef "w_%a(r_%a) = %a # gate %a has %a in the right arg@."
              Var.pp k
              Var.pp g
              F.pp n
              Var.pp g
              Var.pp k) gns) w;
    Var.Map.iter (fun k gns ->
        Var.Map.iter (fun g n ->
            Format.ef "y_%a(r_%a) = %a # gate %a outputs %a@."
              Var.pp k
              Var.pp g
              F.pp n
              Var.pp g
              Var.pp k) gns) y;

    let make_polynomials u =
      Var.Map.of_set vars @@ fun k ->
      let uk = u #! k in
      Polynomial.interpolate
        (List.map (fun (g, rg) ->
             let ukrg (* $u_k(r_g)$ *) = uk #! g in
             rg, ukrg) rk)
    in

    let v = make_polynomials v in
    let w = make_polynomials w in
    let y = make_polynomials y in

    let t = Polynomial.z (List.map (fun (_, i) -> i) rk) in

    { vwy = { v; w; y }; target = t },
    Var.Map.of_list rk

  let decompile  {vwy= { v; w; y }; _} (rs : F.t Var.Map.t) =
    let dom m =
      Var.Set.of_seq @@ Seq.map fst @@ Var.Map.to_seq m
    in
    let domv = dom v in
    let domw = dom w in
    let domy = dom y in
    assert (Var.Set.equal domv domw);
    assert (Var.Set.equal domv domy);
    Var.Map.of_list @@
    Var.Map.fold (fun _g r acc ->
        let f v =
          Var.Map.filter_map (fun _v p ->
              let w = Polynomial.apply p r in
              if F.(w = zero) then None
              else Some w) v
        in
        let v = f v in
        let w = f w in
        let y = f y in
        match Var.Map.bindings y with
        | [y, f] when F.(one = f) -> (y, (v, w)) :: acc
        | _ -> assert false
      ) rs []

  let eval sol { vwy;  target } =
    let eval' (vps : Polynomial.t Var.Map.t) =
      Polynomial.sum
      @@ List.of_seq
      @@ Seq.map (fun (k, p) ->
          let a = sol #! k in
          Polynomial.mul_scalar a p)
      @@ Var.Map.to_seq vps
    in
    let v = eval' vwy.v in
    let w = eval' vwy.w in
    let y = eval' vwy.y in
    let p = Polynomial.Infix.(v * w - y) in
    let h, rem = Polynomial.Infix.(p /% target) in
    assert (Polynomial.is_zero rem);
    p, h

  let test () =
    let x = Var.of_string "i" in
    let e =
      let open Lang in
      let open Expr.Infix in
      let x = Expr.Term (Var x) in
      x * x + x * !2 + !3
    in
    let open Format in
    ef "----------------@.";
    ef "Expr: %a@." Lang.Expr.pp e;

    let circuit = Circuit.of_expr e in
    ef "Gates: @[<v>%a@]@." Circuit.pp circuit;

    let ({ vwy=_; target= t } as qap), _rk = build circuit.gates in
    let sol =
      Result.get_ok
      @@ Circuit.eval (Var.Map.of_list [x, F.of_int 3;
                                        Circuit.one, F.of_int 1]) circuit.gates
    in
    Var.Map.iter (fun v i -> ef "%a = %a@." Var.pp v F.pp i) sol;
    let p, _h = eval sol qap in
    ef "p = %a@." Polynomial.pp p;
    let h, rem = Polynomial.Infix.(p /% t) in
    ef "t = %a@." Polynomial.pp t;
    ef "h = %a@." Polynomial.pp h;
    ef "rem = %a@." Polynomial.pp rem
end
