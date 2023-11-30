(* to avoid silly name crash *)
open Misclib

module Make(F : sig
    include Field.COMPARABLE
    val gen : t Gen.t
  end ) = struct
  module Lang = Lang.Make(F)

  module Circuit = Circuit.Make(F)

  open Circuit

  module Code = struct
    (* Very simple program to compute values of [F.t] *)

    type code =
      | Mul of code * code
      | Div of code * code
      | Not of code
      | Or of code * code
      | Affine of Affine.t
      | Eq of code * code
      | If of code * code * code

    type t = code

    module Combinator = struct
      let ( * ) a b = Mul (a, b)
      let (/) a b = Div (a, b)
      let not a = Not a
      let (||) a b = Or (a, b)
      let (!&) a = Affine a
      let (==) a b = Eq (a, b)
      let if_ a b c = If (a, b, c)
    end

    let rec ptree : t -> Ptree.t =
      fun c ->
      let loc = Location.none in
      match c with
      | Mul (c1, c2) -> [%expr [%e ptree c1] * [%e ptree c2]]
      | Div (c1, c2) -> [%expr [%e ptree c1] / [%e ptree c2]]
      | Not c -> [%expr not [%e ptree c]]
      | Or (c1, c2) -> [%expr [%e ptree c1] || [%e ptree c2]]
      | Affine a -> Circuit.Affine.ptree a
      | Eq (c1, c2) -> [%expr [%e ptree c1] = [%e ptree c2]]
      | If (c1, c2, c3) ->
          [%expr if [%e ptree c1] then [%e ptree c2] else [%e ptree c3]]

    let pp ppf t = Ptree.pp ppf @@ ptree t

    let rec vars =
      let (++) = Var.Set.union in
      function
      | Not t -> vars t
      | Mul (t1, t2)
      | Div (t1, t2)
      | Eq (t1, t2)
      | Or (t1, t2) -> vars t1 ++ vars t2
      | If (t1, t2, t3) -> vars t1 ++ vars t2 ++ vars t3
      | Affine a -> Var.Map.domain a

    type env = F.t Var.Map.t

    let rec eval env =
      let to_bool f =
        if F.(f = zero) then false
        else if F.(f = one) then true
        else assert false
      in
      let of_bool = function
        | false -> F.zero
        | true -> F.one
      in
      function
      | Mul (a, b) ->
          let a = eval env a in
          let b = eval env b in
          F.(a * b)
      | Div (a, b) ->
          let a = eval env a in
          let b = eval env b in
          F.(a / b)
      | Not a ->
          let a = eval env a in
          of_bool @@ not @@ to_bool a
      | Or (a, b) ->
          let a = eval env a in
          let b = eval env b in
          of_bool (to_bool a || to_bool b)
      | Eq (a, b) ->
          let a = eval env a in
          let b = eval env b in
          of_bool F.(a = b)
      | If (a, b, c) ->
          let a = eval env a in
          if to_bool a then eval env b else eval env c
      | Affine a ->
          Var.Map.fold (fun k ck acc ->
              try
                F.(Var.Map.find k env * ck + acc)
              with
              | Not_found ->
                  Format.ef "Var %a not found@." Var.pp k;
                  assert false
            ) a F.zero

    let rec eval_list env = function
      | [] -> env
      | (v,c)::codes ->
          Format.ef "  @[<v2>%a = @[%a@] = ...@]@." Var.pp v pp c;
          let value = eval env c in
          Format.ef "  @[<v2>%a = @[%a@]@]@." Var.pp v F.pp value;
          if Var.Map.mem v env then assert false;
          let env = Var.Map.add v value env in
          eval_list env codes
  end

  let rec components : type a. a Lang.Type.t -> int = function
    | Field | Bool -> 1
    | Pair (t1, t2) -> components t1 + components t2
    | Either (t1, t2) -> max (components t1) (components t2) + 1

  let rec compile_value : type a. a Lang.Type.t -> a Lang.Value.t -> F.t list = fun ty v ->
    match ty, v with
    | _, Field f -> [f]
    | _, Bool true -> [F.one]
    | _, Bool false -> [F.zero]
    | Pair (ty1, ty2), Pair (v1, v2) ->
        compile_value ty1 v1 @ compile_value ty2 v2
    | Either (ty1, _ty2), Left v ->
        let cs = components ty - 1 in
        let fs = compile_value ty1 v in
        F.zero :: fs @ List.init (cs - List.length fs) (fun _ -> F.zero)
    | Either (_ty1, ty2), Right v ->
        let cs = components ty - 1 in
        let fs = compile_value ty2 v in
        F.one :: fs @ List.init (cs - List.length fs) (fun _ -> F.zero)
    | _ -> assert false

  module GateM = struct
    type state =
      { gates : Gate.Set.t;
        inputs : (Lang.security * Lang.Type.packed * Var.t list) String.Map.t;
        rev_codes : (Var.t * Code.t) list; (* reversed order *)
      }

    let init =
      { gates= Gate.Set.empty;
        inputs= String.Map.empty;
        rev_codes= []
      }

    include StateM

    type 'a t = ('a, state) StateM.t

    let add_gate : Affine.t -> Affine.t -> Affine.t -> unit t = fun lhs l r ->
      fun s ->
        (), { s with gates = Gate.Set.add { lhs; l; r } s.gates }

    let add_one : unit t = fun s ->
      (* $ONE may be added more than once *)
      if String.Map.mem "$ONE" s.inputs then (), s
      else
        (),
        { s with
          inputs =
            String.Map.add "$ONE"
              (Lang.Public, Lang.Type.(Packed Field), [Circuit.one]) s.inputs }

    let add_input : type a . string -> Lang.security -> a Lang.Type.t -> _ t =
      fun name sec ty -> fun s ->
      assert (name <> "$ONE");
      if String.Map.mem name s.inputs then invalid_arg "duplicated input name";
      let cs = components ty in
      let vs = List.init cs (fun _ -> Var.make name) in
      List.map Affine.of_var vs,
      { s with inputs = String.Map.add name (sec, Lang.Type.Packed ty, vs) s.inputs }

    let add_code : Var.t -> Code.t -> unit t = fun v e ->
      fun s ->
        if List.mem_assoc v s.rev_codes then assert false;
        (), { s with rev_codes= (v, e) :: s.rev_codes }
  end

  let rec compile1 : type a . (Var.t * Affine.t list) list -> a Lang.Expr.t -> Affine.t GateM.t =
    fun env t ->
    let open GateM.Syntax in
    let+ res = compile env t in
    match res with
    | [af] -> af
    | _ -> assert false

  and compile : type a . (Var.t * Affine.t list) list -> a Lang.Expr.t -> Affine.t list GateM.t =
    let open Lang in
    let open Affine in
    let open Affine.Infix in
    let open GateM in
    let open GateM.Syntax in
    let module ExprC = Expr.Combinator in
    let module CodeC = Code.Combinator in
    let var () =
      let v = Var.make "c" in
      v, of_var v
    in
    let return1 x = return [x] in
    fun env e ->
      match e.desc with
      | Field f ->
          let* () = add_one in
          return1 @@ Affine.of_F f
      | Bool true -> return1 !1
      | Bool false -> return1 !0
      | Input (name, security) ->
          add_input name security e.ty
      | Add (t1, t2) ->
          let* t1 = compile1 env t1 in
          let* t2 = compile1 env t2 in
          return1 @@ t1 + t2
      | Sub (t1, t2) -> compile env ExprC.(t1 + ~- t2)
      | Neg t ->
          let* t = compile1 env t in
          return1 @@ t *$ F.of_int (-1)
      | Mul (t1, t2) ->
          let* t1 = compile1 env t1 in
          let* t2 = compile1 env t2 in
          (match is_const t1, is_const t2 with
           | Some f1, Some f2 -> return1 @@ of_F F.(f1 * f2)
           | Some f1, _ -> return1 @@ t2 *$ f1
           | _, Some f2 -> return1 @@ t1 *$ f2
           | _ ->
               let va, a = var () in
               let* () = add_code va CodeC.(!&t1 * !&t2) in
               let* () = add_gate a t1 t2 in
               return1 a)
      | Div (a, b) ->
          let* a = compile1 env a in
          let* b = compile1 env b in
          (match is_const a, is_const b with
           | Some a, Some b -> return1 @@ of_F F.(a * b)
           | Some a, _ -> return1 @@ b *$ a
           | _, Some b -> return1 @@ a *$ b
           | _ ->
               (* d
                  where
                    d = a * c
                    1 = b * c *)
               let vc, c = var () in
               let vd, d = var () in
               let* () = add_code vc CodeC.(!& !1 / !& b) in
               let* () = add_code vd CodeC.(!&a * !& c) in
               let* () = add_one in
               let* () = add_gate !1 b c in
               let* () = add_gate d a c in
               return1 d)
      | Not { desc= Bool b; _ } -> compile env @@ ExprC.bool (not b)
      | Not a ->
          (* b
             where
               0 = a * b
               1 = a + b
          *)
          let* a = compile1 env a in
          let vb, b = var () in
          let* () = add_code vb CodeC.(not !&a) in
          let* () = add_one in
          let* () = add_gate !0 a b in
          let* () = add_gate !1 (a + b) !1 in
          return1 b
      | And (a, b) ->
          compile env ExprC.(to_field a * to_field b)
      | Or (a, b) ->
          (* c
             where
               c = (a+b) * d
               0 = (a+b) * (1-c)
          *)
          let* a = compile1 env a in
          let* b = compile1 env b in
          let vc, c = var () in
          let vd, d = var () in
          let a_plus_b = a + b in (* a + b creates no gate *)
          let* () = add_one in
          let* () = add_code vc CodeC.(!&a || !&b) in
          let* () = add_code vd CodeC.(if_ !&c (!& !1 / !& a_plus_b) !& !0) in
          let* () = add_gate c a_plus_b d in
          let* () = add_gate !0 a_plus_b (!1 - c) in
          return1 c
      | If (a, b, c) ->
          (* a * b + (1 - a) * c
               = a * b + c - a * c
               = a * (b - c) + c

             c + d
             where
               d = a * (b - c)
          *)
          let* a = compile1 env a in
          (match is_const a with
           | Some a -> compile env @@ if F.(a = of_int 1) then b else c
           | None ->
               let* b = compile env b in
               let* c = compile env c in
               let bc = List.combine b c in
               GateM.mapM (fun (b,c) ->
                   let vd, d = var () in
                   let b_c = b - c in
                   match is_const b_c with
                   | Some b_c ->
                       return @@ c + a *$ b_c
                   | None ->
                       let* () = add_code vd CodeC.(!&a * !&b_c) in
                       let* () = add_gate d a b_c in
                       return @@ c + d)
                 bc)
      | Eq (a, b) ->
          let* a = compile env a in
          let* b = compile env b in
          (match a, b with
          | [a], [b] ->
              (* $a == b$

                 c where
                   1 - c = (a - b) * d
                   0 = (a - b) * c
              *)
              let vc, c = var () in
              let vd, d = var () in
              let* () = add_one in
              let* () = add_code vc CodeC.(!&a == !&b) in
              let* () = add_code vd CodeC.(if_ !&c !& !0 (!& !1 / !&(a - b))) in
              let* () = add_gate (!1 - c) (a - b) d in
              let* () = add_gate !0 (a - b) c in
              return1 c
          | _ ->
              (* $as == bs$

                 ci where
                   1 - ci = (ai - bi) * di
                   0 = (ai - bi) * c
              *)
              let abs = List.combine a b in
              let* cs =
                mapM (fun (a, b) ->
                    let vc, c = var () in
                    let vd, d = var () in
                    let* () = add_one in
                    let* () = add_code vc CodeC.(!&a == !&b) in
                    let* () = add_code vd CodeC.(if_ !&c !& !0 (!& !1 / !&(a - b))) in
                    let* () = add_gate (!1 - c) (a - b) d in
                    let* () = add_gate !0 (a - b) c in
                    return c ) abs
              in
              let* x =
                match cs with
                | [] -> assert false
                | c :: cs ->
                    fold_leftM (fun acc c ->
                        let vx, x = var () in
                        let* () = add_code vx CodeC.(!&acc * !&c) in
                        let* () = add_gate x acc c in
                        return x
                      ) c cs
              in
              return1 x)

      | To_field t -> compile env t

      | Let (v, a, b) ->
          let* a = compile env a in
          let env = (v, a) :: env in
          compile env b
      | Var v -> return @@ List.assoc v env
      | Pair (a, b) ->
          let* a = compile env a in
          let* b = compile env b in
          return (a @ b)
      | Fst a ->
          let cs =
            match a.ty with
            | Pair (t, _) -> components t
            | _ -> assert false
          in
          let* a = compile env a in
          (* TODO: take with length check *)
          return @@ List.take cs a
      | Snd a ->
          let cs =
            match a.ty with
            | Pair (t, _) -> components t
            | _ -> assert false
          in
          let* a = compile env a in
          (* TODO: take with length check *)
          return @@ List.drop cs a
      | Left a ->
          let* a = compile env a in
          return @@ !0 :: a
      | Right a ->
          let* a = compile env a in
          let* () = add_one in
          return @@ !1 :: a
      | Case (ab, va, c, vb, d) ->
          (match ab.ty with
           | Either (aty, bty) ->
               let* ab = compile env ab in
               let tag = List.hd ab in
               let for_a = List.tl @@ List.take Stdlib.(components aty + 1) ab in
               let for_b = List.tl @@ List.take Stdlib.(components bty + 1) ab in
               let* c = compile ((va, for_a) :: env) c in
               let* d = compile ((vb, for_b) :: env) d in
               (* tag= 0 or 1

                  (tag - 1) * c + tag * d

                  x = (tag - 1) * c
                  y = tag * d
                  x + y
               *)
               let* () = add_one in
               let join (c, d) =
                 let vx, x = var () in
                 let vy, y = var () in
                 let* () = add_code vx CodeC.( !&(tag - !1) * !&c ) in
                 let* () = add_gate x (tag - !1) c in
                 let* () = add_code vy CodeC.( !&tag * !&d ) in
                 let* () = add_gate y tag d in
                 return @@ x + y
               in
               mapM join (List.combine c d)
           | _ -> assert false)

  (* If an output affine is more complex than a variable, add a gate
     to add a variable to alias the affine. *)
  let fix_output : Affine.t -> Affine.t GateM.t = fun a ->
    let open GateM in
    let open GateM.Syntax in
    let module CodeC = Code.Combinator in
    match Var.Map.bindings a (* XXX Affine.bindings or to_list *) with
    | [] -> (* zero *)
        return a
    | [v, _] when v = Circuit.one -> (* constant *)
        return a
    | [_v, f] when F.(f = one) ->
        return a
    | [_] -> (* Weighted variable *)
        (* Weird.  Add another gate for a workaround *)
        let vo = Var.make "v" in
        let o = Affine.of_var vo in
        let* () = add_code vo CodeC.(!&a) in
        let* () = add_one in
        let* () = add_gate o a (Affine.Infix.(!) 1) in
        return o
    | _ -> (* Affine *)
        let vo = Var.make "v" in
        let o = Affine.of_var vo in
        let* () = add_code vo CodeC.(!&a) in
        let* () = add_one in
        let* () = add_gate o a (Affine.Infix.(!) 1) in
        return o

  type input_type = Lang.security * Lang.Type.packed * Var.t list

  type input_value = Lang.security * Lang.Value.packed * (Var.t * F.t) list

  type t =
    { gates : Gate.Set.t;
      inputs : input_type String.Map.t;
      inputs_vars : Lang.security Var.Map.t;
      mids : Var.Set.t;
      outputs : Var.Set.t;
      codes : (Var.var * Code.code) list;
      result : Affine.t list;
      circuit : Circuit.t;
    }

  (* Final mending of gates *)
  let compile t =
    let open GateM.Syntax in
    let* a = compile [] t in
    GateM.mapM fix_output a

  let compile t =
    let result, GateM.{ gates; inputs; rev_codes } = compile t GateM.init in

    (* Input variables may be lost in the gates *)
    let inputs_vars =
      let vars = Gate.Set.vars gates in
      String.Map.fold (fun _name (sec, _ty, vs) acc ->
          List.fold_left (fun acc v ->
              if Var.Set.mem v vars then Var.Map.add v sec acc else acc)
            acc vs) inputs Var.Map.empty
    in

    let outputs =
      List.fold_left (fun acc a ->
          match Var.Map.bindings a with
          | [v, _] when v <> Circuit.one -> Var.Set.add v acc
          | [] (* 0 *) -> acc
          | _ -> assert false) Var.Set.empty result
    in
    let mids =
      Var.Set.(diff (Gate.Set.vars gates) (union (Var.Map.domain inputs_vars) outputs))
    in
    let circuit =
      let inputs_public, _inputs_secret =
        Var.Map.partition (fun _ -> function
            | Lang.Secret -> false
            | _ -> true) inputs_vars
      in
      let inputs_public = Var.Map.domain inputs_public in
      let mids = Var.Set.union mids
          Var.Set.(diff (Gate.Set.vars gates) (union inputs_public outputs))
      in
      Circuit.{ gates; inputs_public; outputs; mids }
    in
    { gates; inputs; inputs_vars; mids; outputs; codes= List.rev rev_codes; result; circuit }

  let gen_inputs inputs rng =
    let inputs =
      String.Map.mapi (fun name (sec, Lang.Type.Packed ty, vs) ->
          let (Packed (v, ty) as value) =
            match name with
            | "$ONE" -> Lang.Value.(Packed (Field F.one, Field))
            | _ -> Lang.Value.(Packed (gen ty rng, ty))
          in
          sec, value, List.combine vs (compile_value ty v)) inputs
    in
    let env_lang = String.Map.map (fun (_, v, _) -> v) inputs in
    let env_code =
      String.Map.fold (fun _name (_, _, vs) env_code ->
          List.fold_left (fun env_code (v,f) ->
              Var.Map.add v f env_code) env_code vs) inputs Var.Map.empty
    in
    inputs, env_lang, env_code

  let convert_inputs inputs_type inputs_value =
    let inputs =
      String.Map.mapi (fun name (sec, Lang.Type.Packed ty, vs) ->
          match String.Map.find_opt name inputs_value with
          | None ->
              invalid_argf "convert_inputs: variable not defined: %s" name
          | Some (Lang.Value.Packed (v, ty') as value) ->
              match Lang.Type.equal ty ty' with
              | None -> invalid_argf "convert_inputs: type mismatch: %s" name
              | Some Refl ->
                  sec, value, List.combine vs (compile_value ty v)) inputs_type
    in
    let env_code =
      String.Map.fold (fun _name (_, _, vs) env_code ->
          List.fold_left (fun env_code (v,f) ->
              Var.Map.add v f env_code) env_code vs) inputs Var.Map.empty
    in
    inputs, env_code

  let test e =
    let open Format in
    ef "code: %a@." Lang.Expr.pp e;
    let { gates; inputs; inputs_vars; outputs; codes; result; _ }  = compile e in

    ef "public inputs: @[%a@]@."
      (list ",@ " (fun ppf v -> Var.pp ppf v))
    @@ List.filter_map (function (v, Lang.Public) -> Some v | _ -> None)
    @@ Var.Map.bindings inputs_vars;

    ef "secret inputs: @[%a@]@."
      (list ",@ " (fun ppf v -> Var.pp ppf v))
    @@ List.filter_map (function (v, Lang.Secret) -> Some v | _ -> None)
    @@ Var.Map.bindings inputs_vars;

    ef "outputs: @[%a@]@."
      (list ",@ " Var.pp)
    @@ Var.Set.elements outputs;

    ef "gates: @[<v>%a@]@." Circuit.Gate.Set.pp gates;

    ef "code: @[<v>%a@]@."
      (list "@," (fun ppf (v, e) -> f ppf "let %a = %a" Var.pp v Code.pp e))
      codes;

    prerr_endline "Lang.eval";

    let rng = Gen.init_auto () in
    let inputs, env_lang, env_code = gen_inputs inputs rng in

    Format.(ef "Input_values: @[<v>%a@]@."
              (list ",@ " (fun ppf (name, (sec, Lang.Value.Packed (v, _ty), _)) ->
                   f ppf "%s : %a = %a" name Lang.pp_security sec Lang.Value.pp v))
            @@ String.Map.bindings inputs);

    let o_lang = Lang.Eval.eval env_lang e in
    Format.(ef "Output: @[%a@]@." Lang.Value.pp o_lang);

    let o = compile_value e.ty o_lang in

    prerr_endline "Code.eval";
    let env = Code.eval_list env_code codes in
    let o' = List.map (Circuit.Affine.eval env) result in
    assert (o = o');

    prerr_endline "test done"
end

let test () =
  let module Comp = Make(Ecp.Bls12_381.Fr) in
  let module Lang = Comp.Lang in
  let open Lang.Expr.Combinator in

  Comp.test begin
    let_ (input "input" secret ty_field) (fun x -> if_ (x == !0) !1 !2)
  end;

  Comp.test begin
    let_ (input "input" secret ty_field) (fun x -> pair (x + !1) (x * !2))
  end
