open Utils

module Make(F : Field.COMPARABLE) = struct

  module Circuit = Circuit.Make(F)

  module Syntax = struct

    type 'a ty =
      | Field : F.t ty
      | Bool : bool ty

    type security = Public | Secret

    (** Type of ZK computation *)
    type 'a t =
      | Field : F.t -> F.t t
      | Bool : bool -> bool t
      | Add : F.t t * F.t t -> F.t t
      | Sub : F.t t * F.t t -> F.t t
      | Mul : F.t t * F.t t -> F.t t
      | Div : F.t t * F.t t -> F.t t
      | Input : security * 'a ty -> 'a t
      | Not : bool t -> bool t
      | And : bool t * bool t -> bool t
      | Or : bool t * bool t -> bool t
      | If : bool t * 'a t * 'a t -> 'a t
      | Eq : 'a t * 'a t -> bool t
      | To_field : _ t -> F.t t (* cast *)
      | Cast : _ t -> 'a t
      | Let : Var.t * 'a t * 'b t -> 'b t
      | Var : Var.t -> 'a t

    let rec ptree : type a. a t -> Ppxlib_ast.Ast.expression =
      let loc = Location.none in
      let open Ppxlib_ast.Ast_helper in
      function
      | Field f -> Exp.constant @@ Const.integer (Format.asprintf "%a" F.pp f)
      | Bool true -> [%expr true]
      | Bool false -> [%expr false]
      | Add (t1, t2) -> [%expr [%e ptree t1] + [%e ptree t2]]
      | Sub (t1, t2) -> [%expr [%e ptree t1] - [%e ptree t2]]
      | Mul (t1, t2) -> [%expr [%e ptree t1] * [%e ptree t2]]
      | Div (t1, t2) -> [%expr [%e ptree t1] / [%e ptree t2]]
      | Input (Public, _) -> Exp.ident { txt= Longident.Lident "public"; loc= Location.none }
      | Input (Secret, _) -> Exp.ident { txt= Longident.Lident "secret"; loc= Location.none }
      | Var v -> Exp.ident { txt= Longident.Lident (Var.to_string v); loc= Location.none }
      | Not b -> [%expr not [%e ptree b]]
      | And (t1, t2) -> [%expr [%e ptree t1] && [%e ptree t2]]
      | Or (t1, t2) -> [%expr [%e ptree t1] || [%e ptree t2]]
      | If (t1, t2, t3) -> [%expr if [%e ptree t1] then [%e ptree t2] else [%e ptree t3]]
      | Eq (t1, t2) -> [%expr [%e ptree t1] == [%e ptree t2]]
      | To_field t -> [%expr to_field [%e ptree t]]
      | Let (v, t1, t2) -> [%expr let [%p Pat.var {txt= Var.to_string v; loc= Location.none}] = [%e ptree t1] in [%e ptree t2]]
      | Cast t -> ptree t

    let pp ppf t = Ppxlib_ast.Pprintast.expression ppf @@ ptree t

    let var =
      let cntr = ref 0 in
      fun () ->
        incr cntr;
        Var.of_string (Printf.sprintf "v%d" !cntr)

    module S = struct

      let ty_field : _ ty = Field
      let ty_bool : _ ty = Bool

      let public = Public
      let secret = Secret

      type nonrec security = security = Public | Secret

      let (+) a b =
        match a, b with
        | Field a, Field b -> Field F.(a + b)
        | Field a, _ when F.(a = zero) -> b
        | _, Field b when F.(b = zero) -> a
        | _ -> Add (a, b)

      let (-) a b =
        match a, b with
        | Field a, Field b -> Field F.(a - b)
        | _, Field b when F.(b = zero) -> a
        | _ -> Sub (a, b)

      let ( * ) a b =
        match a, b with
        | Field a, Field b -> Field F.(a * b)
        | _, Field b when F.(b = one) -> a
        | Field a, _ when F.(a = one) -> b
        | _ -> Mul (a, b)

      let (/) a b =
        match a, b with
        | Field a, Field b -> Field F.(a / b)
        | _, Field b when F.(b = one) -> a
        | _ -> Div (a, b)

      let bool b = Bool b

      let not a =
        match a with
        | Bool b -> Bool (not b)
        | _ -> Not a

      let (&&) a b = And (a, b)
      let (||) a b = Or (a, b)
      let if_ a b c = If (a, b, c)

      let field n = Field n

      let (!) n = Field (F.of_int n)

      let input sec ty = Input (sec, ty)

      let to_field : type a. a t -> F.t t = fun t ->
        match t with
        | Field _ -> t
        | _ -> To_field t

      let var v = Var v

      let let_ v a b = Let (v, a, b)

      let (==) a b = Eq (a, b)

      let cast a = Cast a
    end
  end

  open Circuit

  let (++) = Gate.Set.union

  let gate lhs l r = Gate.Set.singleton Gate.{ lhs; l; r }

  type binding = Var.t * Affine.t

  type env = binding list

  type syntax' = Syntax' : 'a Syntax.t -> syntax'

  let rec compile
    : type a . env -> a Syntax.t
      -> (Affine.t * Gate.Set.t) * (a Syntax.t * (Var.t * syntax') list)
    = fun env t ->
      let open Circuit in
      let open Affine in
      let open Affine.Infix in
      match t with
      | Cast _ -> assert false

      | Input (_sec, _ty) ->
          (* v * 1 *)
          let v = Syntax.var () in
          (of_var v, Gate.Set.empty),
          (t, [])

      | Field f ->
          (* $ONE * f *)
          (of_F f, Gate.Set.empty),
          (t, [])

      | Bool b ->
          (* $ONE * 1/0 *)
          (!(if b then 1 else 0), Gate.Set.empty),
          (Syntax.S.(bool b), [])

      | Add (a, b) ->
          (* a + b *)
          let (a, gsa), (ta, dsa) = compile env a in
          let (b, gsb), (tb, dsb) = compile env b in
          (a + b, gsa ++ gsb),
          (Syntax.S.(ta + tb), dsa @ dsb)

      | Sub (a, b) ->
          (* $a + (-1) * b$ *)
          let (a, gsa), (ta, dsa) = compile env a in
          let (b, gsb), (tb, dsb) = compile env b in
          (a + b *$ (F.of_int (-1)), gsa ++ gsb),
          (Syntax.S.(ta - tb), dsa @ dsb)

      | Mul (a, b) ->
          (* c * 1 = a * b *)
          let (a, gsa), (ta, dsa) = compile env a in
          let (b, gsb), (tb, dsb) = compile env b in
          let vc = Syntax.var () in
          (match is_const a with
           | Some a ->
               (b *$ a, gsa ++ gsb), (Syntax.S.(ta * tb), dsa @ dsb)
           | None ->
               match is_const b with
               | Some b ->
                   (a *$ b, gsa ++ gsb), (Syntax.S.(ta * tb), dsa @ dsb)
               | None ->
                   let c = Affine.of_var vc in
                   (c, gate c a b ++ gsa ++ gsb),
                   (Syntax.S.(var vc), Syntax.S.(vc, Syntax' (ta * tb)) :: dsa @ dsb))

      | To_field a ->
          let (a, gsa), (ta, dsa) = compile env a in
          (a, gsa), (Syntax.S.to_field ta, dsa)

      | Div (a, b) ->
          (* a / b

             d
             where
               d = a * c
               1 = b * c *)
          let (a, gsa), (ta, dsa) = compile env a in
          let (b, gsb), (tb, dsb) = compile env b in
          let vc = Syntax.var () in
          let vd = Syntax.var () in
          let c = Affine.of_var vc in
          let d = Affine.of_var vd in
          (d, gate d a c ++ gate !1 b c ++ gsa ++ gsb),
          Syntax.S.(var vd, ((vd, Syntax' (ta / tb)) :: dsa @ dsb))

      | Not a ->
          (* b
             where
               0 = a * b
               1 = a + b
          *)
          let (a, gsa), (ta, dsa) = compile env a in
          let vb = Syntax.var () in
          let b = Affine.of_var vb in
          (b, gate !0 a b ++ gate !1 (a + b) !1 ++ gsa),
          Syntax.S.(var vb, (vb, Syntax' (not ta)) :: dsa)

      | And (a, b) ->
          let (a, gsa), (ta, dsa) = compile env a in
          let (b, gsb), (tb, dsb) = compile env b in
          let vc = Syntax.var () in
          let c = Affine.of_var vc in
          (c, gate c a b ++ gsa ++ gsb),
          Syntax.S.(var vc, (vc, Syntax' (ta && tb)) :: dsa @ dsb)

      | Or (a, b) ->
          (* c = a || b

             c
             where
               c = (a+b) * d
               0 = (a+b) * (1-c)
          *)
          let (a, gsa), (ta, dsa) = compile env a in
          let (b, gsb), (tb, dsb) = compile env b in
          let vc = Syntax.var () in
          let vd = Syntax.var () in
          let c = Affine.of_var vc in
          let d = Affine.of_var vd in
          (c, gate c (a + b) d ++ gate !0 (a + b) (!1 - c) ++ gsa ++ gsb),
          Syntax.S.(var vc,
                    (vd, Syntax' (if_ (var vc) (!1 / (to_field ta + to_field tb)) !1))
                    :: (vc, Syntax' (ta || tb))
                    :: dsa @ dsb)

      | If (a, b, c) ->
          (* a * b + (1 - a) * c
               = a * b + c - a * c
               = a * (b - c) + c

             c + d
             where
               d = a * (b - c)
          *)
          let (a, gsa), (ta, dsa) = compile env a in
          let (b, gsb), (tb, dsb) = compile env b in
          let (c, gsc), (tc, dsc) = compile env c in
          let vd = Syntax.var () in
          let d = Affine.of_var vd in
          (c + d, gate d a (b - c) ++ gsa ++ gsb ++ gsc),
          Syntax.S.(cast (to_field tc + var vd),
                    (vd, Syntax' (to_field ta * (to_field tb - to_field tc))) :: dsa @ dsb @ dsc)

      | Eq (a, b) ->
          (* $a == b$

             c where
               1 - c = (a - b) * d
               0 = (a - b) * c
          *)
          let (a, gsa), (ta, dsa) = compile env a in
          let (b, gsb), (tb, dsb) = compile env b in
          let vc = Syntax.var () in
          let vd = Syntax.var () in
          let c = Affine.of_var vc in
          let d = Affine.of_var vd in
          (c, gate (!1 - c) (a - b) d ++ gate !0 (a - b) c ++ gsa ++ gsb),
          Syntax.S.(var vc, (vd, Syntax' (if_ (var vc) !1 (!1 / (to_field ta - to_field tb))))
                            :: (vc, Syntax' (ta == tb))
                            :: dsa @ dsb)

      | Let (v, a, b) ->
          let (a, gsa), (ta, dsa) = compile env a in
          let env = (v, a) :: env in
          let (b, gsb), (tb, dsb) = compile env b in
          (b, gsa ++ gsb),
          (tb, dsb @ (v, Syntax' ta) :: dsa)

      | Var v ->
          match List.assoc_opt v env with
          | None ->
              failwithf "Zukelang.Make(_).Comp.compile: variable %a not found" Var.pp v
          | Some a ->
              (a, Gate.Set.empty), Syntax.S.(var v, [])

  let compile e =
    let (a, gates), eval = compile [] e in
    let outvar, gates =
      match Var.Map.bindings a with
      | [v, _f] when v = Circuit.one -> None, gates
      | [v, f] when F.(f = one) -> Some v, gates
      | _ ->
          let open Circuit.Affine in
          let open Circuit.Affine.Infix in
          let v = Syntax.var () in
          Some v, gate (of_var v) a !1 ++ gates
    in
    let eval =
      let e, bindings = eval in
      let e =
        match outvar with
        | None -> e
        | Some v -> Syntax.S.(let_ v e (var v))
      in
      List.fold_left (fun acc (v, Syntax' e) ->
          Syntax.S.(let_ v e acc)) e bindings
    in
    outvar, gates, eval
end

let test () =
  let module Comp = Make(Ecp.Bls12_381.Fr) in
  let module Circuit = Circuit.Make(Ecp.Bls12_381.Fr) in
  let e = Comp.Syntax.S.(let x = Comp.Syntax.var () in
                         let_ x (input secret ty_field) (if_ (var x == !0) !1 !2)) in
  Format.ef "code: %a@." Comp.Syntax.pp e;
  let _outvar, gates, eval = Comp.compile e in
  Format.ef "eval: %a@." Comp.Syntax.pp eval;
  Format.ef "gates: @[<v>%a@]@." Circuit.Gate.Set.pp gates
