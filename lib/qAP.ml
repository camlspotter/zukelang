open Misc

open Var.Infix

type 'a vwy = { v : 'a; w : 'a; y : 'a }

module Make(F : Field.COMPARABLE) = struct

  type nonrec 'a vwy = 'a vwy = { v : 'a; w : 'a; y : 'a }

  module Polynomial = Polynomial.Make(F)
  module Lang = Lang.Make(F)
  module Circuit = Circuit.Make(F)
  module IntMap = Map.Make(Int)

  type t =
    { vwy : Polynomial.t Var.Map.t vwy;
      target : Polynomial.t
    }

  let build (gates : Circuit.Gate.Set.t) =
    let vars = Circuit.vars gates in

    (* $r_g$: gate id *)
    let rgs = List.mapi (fun rg g -> rg, g) @@ Circuit.Gate.Set.elements gates in

    (* variable -> gate_id -> weight *)
    let make_matrix f =
      Var.Map.of_set vars @@ fun k ->
      IntMap.of_seq @@ Seq.map (fun (rg, g) -> rg, f k g) @@ List.to_seq rgs
    in

    let v =
      (* $v_k(r_g) = 1$ when gate $g$ has $c_k$ at the left of op *)
      make_matrix @@ fun k Circuit.Gate.{l; _} ->
      match Var.Map.find_opt k l with
      | None -> F.zero
      | Some n -> n
    in

    let w =
      (* $w_k(r_g) = 1$ when gate $g$ has $c_k$ at the right of op *)
      make_matrix @@ fun k Circuit.Gate.{r; _} ->
      match Var.Map.find_opt k r with
      | None -> F.zero
      | Some n -> n
    in

    let y =
      (* $y_k(r_g) = 1$ when gate (v, _, _) , $v = c_k$ *)
      make_matrix @@ fun k Circuit.Gate.{lhs; _} ->
      match Var.Map.find_opt k lhs with
      | None -> F.zero
      | Some n -> n
    in

    Var.Map.iter (fun k gns ->
        IntMap.iter (fun rg n ->
            Format.ef "v_%a(r_%d) = %a # gate %d has %a in the left arg@."
              Var.pp k
              rg
              F.pp n
              rg
              Var.pp k) gns) v;
    Var.Map.iter (fun k gns ->
        IntMap.iter (fun rg n ->
            Format.ef "w_%a(r_%d) = %a # gate %d has %a in the right arg@."
              Var.pp k
              rg
              F.pp n
              rg
              Var.pp k) gns) w;
    Var.Map.iter (fun k gns ->
        IntMap.iter (fun rg n ->
            Format.ef "y_%a(r_%d) = %a # gate %d has %a in the LHS@."
              Var.pp k
              rg
              F.pp n
              rg
              Var.pp k) gns) y;

    let make_polynomials (u : F.t IntMap.t Var.Map.t) : Polynomial.t Var.Map.t =
      Var.Map.map (fun imap ->
          Polynomial.interpolate
            (List.map (fun (rg, f) -> F.of_int rg, f)
             @@ IntMap.bindings imap)) u
    in

    let v = make_polynomials v in
    let w = make_polynomials w in
    let y = make_polynomials y in

    let t = Polynomial.z (List.map (fun (rg, _) -> F.of_int rg) rgs) in

    { vwy = { v; w; y }; target = t }, rgs

  let decompile {vwy= { v; w; y }; _} (rgs : (int * Circuit.Gate.t) list) =
    let dom m =
      Var.Set.of_seq @@ Seq.map fst @@ Var.Map.to_seq m
    in
    let domv = dom v in
    let domw = dom w in
    let domy = dom y in
    assert (Var.Set.equal domv domw);
    assert (Var.Set.equal domv domy);
    Circuit.Gate.Set.of_list @@
    List.fold_left (fun acc (rg, _g) ->
        let rg = F.of_int rg in
        let f v =
          Var.Map.filter_map (fun _v p ->
              let w = Polynomial.apply p rg in
              if F.(w = zero) then None
              else Some w) v
        in
        let l = f v in
        let r = f w in
        let lhs = f y in
        Circuit.Gate.{ lhs; l; r } :: acc
      ) [] rgs

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
