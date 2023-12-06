open Misclib
open Typedtree
open Zk

module Make(F : Curve.F) = struct

  module Lang = Lang.Make(F)

  exception Illegal of Location.t * string

  let () = Exn.register_printer @@ function
    | Illegal (loc, s) ->
        Some (fun ppf -> Format.f ppf "%a: %s" Location.print_loc loc s)
    | _ -> None

  let illegalf loc fmt =
    Format.kasprintf (fun s -> raise (Illegal (loc, s))) fmt

  let type_ loc (ty: Types.type_expr) : Lang.Type.packed =
    let rec f (ty : Types.type_expr) =
      match (Types.Transient_expr.repr ty).desc with
      | Tvar _ -> illegalf loc "Type variable not supported"
      | Tarrow _ -> illegalf loc "Arrow not supported "
      | Ttuple [t1; t2] ->
          let Lang.Type.Packed t1 = f t1 in
          let Packed t2 = f t2 in
          Packed (Pair (t1, t2))
      | Tconstr (p, _, _) when p = Predef.path_int ->
          Packed Field
      | Tconstr (p, _, _) when p = Predef.path_bool ->
          Packed Bool
      | Tconstr (p, args, _) ->
          (match p, args with
           | Pdot (Pdot (Pident _, "Either"), "t"), [t1; t2] ->
               let Packed t1 = f t1 in
               let Packed t2 = f t2 in
               Packed (Either (t1, t2))
           | p, _ -> illegalf loc "Unknown data type: %s" (Path.name p))
      | _ -> illegalf loc "Unsupported type"
    in
    try f ty with
    | Illegal _ as exn ->
        Format.eprintf "Error: %a@." Printtyp.type_scheme ty;
        raise exn

  let rec expr env (e : Typedtree.expression) : Lang.Expr.packed =
    let open Lang.Expr in
    let module C = Lang.Expr.Combinator in
    let unpack' ty a = Option.get @@ unpack ty a in
    match e.exp_desc with
    | Texp_ident (Pident id, _, _vd) ->
        (match List.assoc_opt (Ident.name id) env with
         | None -> assert false
         | Some packed -> packed)
    | Texp_constant (Const_int i) -> Packed C.(field (F.of_int i))
    | Texp_construct ({txt=Lident "true"; _}, _, []) -> Packed C.(bool true)
    | Texp_construct ({txt=Lident "false"; _}, _, []) -> Packed C.(bool false)

    | Texp_construct ({txt=Ldot (Lident "Either", "Left"); _}, _, [a]) ->
        let Packed ty = type_ e.exp_loc e.exp_type in
        (match ty with
         | Either (ty1, ty2) ->
             let a = unpack' ty1 @@ expr env a in
             Packed C.(left a ty2)
         | _ -> assert false)

    | Texp_construct ({txt=Ldot (Lident "Either", "Right"); _}, _, [a]) ->
        let Packed ty = type_ e.exp_loc e.exp_type in
        (match ty with
         | Either (ty1, ty2) ->
             let a = unpack' ty2 @@ expr env a in
             Packed C.(right ty1 a)
         | _ -> assert false)

    | Texp_let (Nonrecursive, [b], body) ->
        let Packed ty = type_ e.exp_loc e.exp_type in
        (match b.vb_pat.pat_desc with
         | Tpat_var (_, {txt; _}) ->
             let Packed def = expr env b.vb_expr in
             Packed (
               C.let_ def (fun def ->
                   let env = (txt, Packed def) :: env in
                   let body = expr env body in
                   unpack' ty body))
         | _ ->
             illegalf b.vb_pat.pat_loc "Complex pattern is not supported")
    | Texp_let (Nonrecursive, _, _) ->
        illegalf e.exp_loc "Recursive let is not supported"
    | Texp_let (Recursive, _, _) ->
        illegalf e.exp_loc "Recursive let is not supported"
    | Texp_ifthenelse (a, b, Some c) ->
        let a = unpack' Bool @@ expr env a in
        let Packed b = expr env b in
        let c = unpack' b.ty @@ expr env c in
        Packed (C.if_ a b c)
    | Texp_ifthenelse (_, _, None) ->
        illegalf e.exp_loc "else less if is not supported"
    | Texp_tuple [a; b] ->
        let Packed a = expr env a in
        let Packed b = expr env b in
        Packed (C.pair a b)
    | Texp_tuple _ ->
        illegalf e.exp_loc "3 or more tuples are not supported "
    | Texp_apply (f, args) ->
        let id =
          match f.exp_desc with
          | Texp_ident (_, {txt=Lident s; _}, _) -> s
          | _ -> illegalf f.exp_loc "Functions can only be identifiers"
        in
        (match id with
         | "secret" | "public" ->
             let security = match id with "secret" -> Lang.Secret | "public" -> Public | _ -> assert false in
             let n =
               match args with
               | [ Nolabel, Some { exp_desc= Texp_constant (Const_string (s, _, _)); _ } ] -> s
               | _ -> illegalf e.exp_loc "secret and public must take a string literal"
             in
             let Packed ty = type_ e.exp_loc e.exp_type in
             Packed (C.input n security ty)
         | _ ->
             let args =
               List.map (function
                   | (Asttypes.Nolabel, Some e) -> expr env e
                   | _ -> illegalf e.exp_loc "Invalid application") args
             in
             match id, args with
             | "+", [a; b] ->
                 Packed C.(unpack' Field a + unpack' Field b)
             | "-", [a; b] ->
                 Packed C.(unpack' Field a - unpack' Field b)
             | "*", [a; b] ->
                 Packed C.(unpack' Field a * unpack' Field b)
             | "/", [a; b] ->
                 Packed C.(unpack' Field a / unpack' Field b)
             | "~-", [a] ->
                 Packed C.(~- (unpack' Field a))
             | "not", [a] ->
                 Packed C.(not @@ unpack' Bool a)
             | "&&", [a; b] ->
                 Packed C.(unpack' Bool a && unpack' Bool b)
             | "||", [a; b] ->
                 Packed C.(unpack' Bool a || unpack' Bool b)
             | "==", [Packed ({ty=tya; _} as a);
                      Packed ({ty=tyb; _} as b)] ->
                 (match Lang.Type.equal tya tyb with
                  | None -> assert false
                  | Some Refl -> Packed C.(a == b))
             | "fst", [a] ->
                 (match a with
                  | Packed ({ ty= Pair _; _ } as a) -> Packed C.(fst a)
                  | _ -> assert false)
             | "snd", [a] ->
                 (match a with
                  | Packed ({ ty= Pair _; _ } as a) -> Packed C.(snd a)
                  | _ -> assert false)
             | "left", [Packed a] ->
                 let ty = type_ e.exp_loc e.exp_type in
                 (match ty with
                  | Packed (Either (tyl, tyr)) ->
                      (match Lang.Type.equal tyl a.ty with
                       | None -> assert false
                       | Some Refl -> Packed C.(left a tyr))
                  | _ -> assert false)
             | "right", [Packed a] ->
                 let ty = type_ e.exp_loc e.exp_type in
                 (match ty with
                  | Packed (Either (tyl, tyr)) ->
                      (match Lang.Type.equal tyr a.ty with
                       | None -> assert false
                       | Some Refl -> Packed C.(right tyl a))
                  | _ -> assert false)
             | _ -> illegalf e.exp_loc "Invalid application")
    | _ ->
        Format.eprintf "expr: %a@."
          Pprintast.expression (Untypeast.untype_expression e);
        illegalf e.exp_loc "Unsupported language construct"


  let expr env e = Exn.catch (fun () -> expr env e)

  let extend_env env =
    let ty =
      let a = Btype.newgenvar () in
      Btype.newgenty (Tarrow (Nolabel, Predef.type_string, a, Types.commu_var ()))
    in
    let vd = Types.{ val_type= ty; (* string -> 'a *)
                     val_kind= Val_reg;
                     val_loc= Location.none;
                     val_attributes= [];
                     val_uid = Shape.Uid.mk ~current_unit:"foobar"
                   }
    in
    let env = Env.add_value (Ident.create_persistent "secret") vd env in
    Env.add_value (Ident.create_persistent "public") vd env

  let f e =
    Result.bind (Typecheck.expression extend_env e)
    @@ fun typed ->
    match typed.structure.str_items with
    | [ i ] ->
        (match i.str_desc with
         | Tstr_eval (e, _) -> expr [] e
         | _ -> assert false)
    | _ -> assert false
end
