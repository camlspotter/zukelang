(* to avoid silly name crash *)
module ZLang = Lang

open Utils

module Lang = ZLang

module Make(F : Field.COMPARABLE) = struct
  module Lang = Lang.Make(F)

  module Circuit = Circuit.Make(F)

  open Circuit

  let (++) = Gate.Set.union

  let gate lhs l r = Gate.Set.singleton Gate.{ lhs; l; r }

  type binding = Var.t * Affine.t

  type env = binding list

  type syntax' = Syntax' : 'a Lang.t -> syntax'

  let rec compile
    : type a . env -> a Lang.t
      -> (Affine.t * Gate.Set.t) * a Lang.t
    = fun env t ->
      let open Circuit in
      let open Affine in
      let open Affine.Infix in
      let empty = Gate.Set.empty in
      let module K = struct
        let (+) (a, gsa) (b, gsb) = a + b, gsa ++ gsb
        and (-) (a, gsa) (b, gsb) = a + b *$ (F.of_int (-1)), gsa ++ gsb
        and ( *$ ) (a, gsa) f = a *$ f, gsa
        and ( * ) (a, gsa) (b, gsb) =
          let vc = Lang.var () in
          match is_const a with
          | Some a -> (b *$ a, gsa ++ gsb)
           | None ->
               match is_const b with
               | Some b -> (a *$ b, gsa ++ gsb)
               | None ->
                   let c = Affine.of_var vc in
                   (c, gate c a b ++ gsa ++ gsb)
      end in
      match t with
      | Cast _ -> assert false

      | Input (_sec, _ty) ->
          (* v * 1 *)
          let v = Lang.var () in
          (of_var v, empty),
          t

      | Field f ->
          (* $ONE * f *)
          (of_F f, empty),
          t

      | Bool b ->
          (* $ONE * 1/0 *)
          (!(if b then 1 else 0), empty),
          Lang.S.(bool b)

      | Add (a, b) ->
          (* a + b *)
          let a, ta = compile env a in
          let b, tb = compile env b in
          K.(a + b),
          Lang.S.(in_let2 ta tb (+))

      | Sub (a, b) ->
          (* $a + (-1) * b$ *)
          let a, ta = compile env a in
          let b, tb = compile env b in
          K.(a - b),
          Lang.S.(in_let2 ta tb (-))

      | Mul (a, b) ->
          (* c * 1 = a * b *)
          let (a, gsa), ta = compile env a in
          let (b, gsb), tb = compile env b in
          let vc = Lang.var () in
          (match is_const a with
           | Some a ->
               assert (Gate.Set.is_empty gsa);
               (b *$ a, gsb), Lang.S.(in_let2 ta tb ( * ))
           | None ->
               match is_const b with
               | Some b ->
                   assert (Gate.Set.is_empty gsb);
                   (a *$ b, gsa), Lang.S.(in_let2 ta tb ( * ))
               | None ->
                   let c = Affine.of_var vc in
                   (c, gate c a b ++ gsa ++ gsb),
                   Lang.S.(in_let2 ta tb @@ fun ta tb -> let_ vc (ta * tb) (var vc)))

      | To_field a ->
          let a, ta = compile env a in
          a, Lang.S.(in_let ta to_field)

      | Div (a, b) ->
          (* a / b

             d
             where
               d = a * c
               1 = b * c *)
          let (a, gsa), ta = compile env a in
          let (b, gsb), tb = compile env b in
          let vc = Lang.var () in
          let vd = Lang.var () in
          let c = Affine.of_var vc in
          let d = Affine.of_var vd in
          (d, gate d a c ++ gate !1 b c ++ gsa ++ gsb),
          Lang.S.(in_let2 ta tb @@ fun ta tb -> let_ vd (ta / tb) (var vd))

      | Not a ->
          (* b
             where
               0 = a * b
               1 = a + b
          *)
          let (a, gsa), ta = compile env a in
          let vb = Lang.var () in
          let b = Affine.of_var vb in
          (b, gate !0 a b ++ gate !1 (a + b) !1 ++ gsa),
          Lang.S.(in_let ta @@ fun ta -> not ta)

      | And (a, b) ->
          let (a, gsa), ta = compile env a in
          let (b, gsb), tb = compile env b in
          let vc = Lang.var () in
          let c = Affine.of_var vc in
          (c, gate c a b ++ gsa ++ gsb),
          Lang.S.(in_let2 ta tb @@ fun ta tb -> let_ vc (ta && tb) (var vc))

      | Or (a, b) ->
          (* c = a || b

             c
             where
               c = (a+b) * d
               0 = (a+b) * (1-c)
          *)
          let (a, gsa), ta = compile env a in
          let (b, gsb), tb = compile env b in
          let vc = Lang.var () in
          let vd = Lang.var () in
          let c = Affine.of_var vc in
          let d = Affine.of_var vd in
          (c, gate c (a + b) d ++ gate !0 (a + b) (!1 - c) ++ gsa ++ gsb),
          Lang.S.(in_let2 ta tb @@ fun ta tb ->
              let_ vc (ta || tb)
              @@ let_ vd (if_ (var vc) (!1 / (to_field ta + to_field tb)) !1)
                (var vc))

      | If (a, b, c) ->
          (* a * b + (1 - a) * c
               = a * b + c - a * c
               = a * (b - c) + c

             c + d
             where
               d = a * (b - c)
          *)
          let (a, gsa), ta = compile env a in
          let (b, gsb), tb = compile env b in
          let (c, gsc), tc = compile env c in
          let vd = Lang.var () in
          let d = Affine.of_var vd in
          (c + d, gate d a (b - c) ++ gsa ++ gsb ++ gsc),
          Lang.S.(in_let2 ta tb @@ fun ta tb ->
              let_ vd (to_field ta * (to_field tb - to_field tc))
              @@ cast (to_field tc + var vd))

      | Eq (a, b) ->
          (* $a == b$

             c where
               1 - c = (a - b) * d
               0 = (a - b) * c
          *)
          let (a, gsa), ta = compile env a in
          let (b, gsb), tb = compile env b in
          let vc = Lang.var () in
          let vd = Lang.var () in
          let c = Affine.of_var vc in
          let d = Affine.of_var vd in
          (c, gate (!1 - c) (a - b) d ++ gate !0 (a - b) c ++ gsa ++ gsb),
          Lang.S.(in_let2 ta tb @@ fun ta tb ->
              let_ vc (ta == tb)
              @@ let_ vd (if_ (var vc) !1 (!1 / (to_field ta - to_field tb)))
                (var vc))

      | Let (v, a, b) ->
          let (a, gsa), ta = compile env a in
          let env = (v, a) :: env in
          let (b, gsb), tb = compile env b in
          (b, gsa ++ gsb),
          Lang.S.(let_ v ta tb)

      | Var v ->
          match List.assoc_opt v env with
          | None ->
              failwithf "Zukelang.Make(_).Comp.compile: variable %a not found" Var.pp v
          | Some a ->
              (a, empty), Lang.S.var v

  let compile e =
    let (a, gates), eval = compile [] e in
    let outvar, gates =
      match Var.Map.bindings a with
      | [v, _f] when v = Circuit.one -> None, gates
      | [v, f] when F.(f = one) -> Some v, gates
      | _ ->
          let open Circuit.Affine in
          let open Circuit.Affine.Infix in
          let v = Lang.var () in
          Some v, gate (of_var v) a !1 ++ gates
    in
    let eval =
      match outvar with
      | None -> eval
      | Some v -> Lang.S.(let_ v eval (var v))
    in
    outvar, gates, eval
end

let test () =
  let module Comp = Make(Ecp.Bls12_381.Fr) in
  let module Lang = Comp.Lang in
  let module Circuit = Comp.Circuit in
  let e = Lang.S.(let x = Lang.var () in
                  let_ x (input secret ty_field) (if_ (var x == !0) !1 !2)) in
  Format.ef "code: %a@." Lang.pp e;
  let _outvar, gates, eval = Comp.compile e in
  Format.ef "eval: %a@." Lang.pp eval;
  Format.ef "gates: @[<v>%a@]@." Circuit.Gate.Set.pp gates
