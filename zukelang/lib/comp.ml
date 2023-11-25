(* to avoid silly name crash *)
module ZKLang = Lang

open Utils

module Make(F : sig
    include Field.COMPARABLE
    val gen : t Gen.t
  end ) = struct
  module Lang = ZKLang.Make(F)

  module Circuit = Circuit.Make(F)

  open Circuit

  module Code = struct
    type code =
      | Mul of code * code
      | Div of code * code
      | Not of code
      | Or of code * code
      | Affine of Affine.t
      | Eq of code * code
      | If of code * code * code

    type t = code

    module S = struct
      let ( * ) a b = Mul (a, b)
      let (/) a b = Div (a, b)
      let not a = Not a
      let (||) a b = Or (a, b)
      let (!&) a = Affine a
      let (==) a b = Eq (a, b)
      let if_ a b c = If (a, b, c)
    end

    let rec pp ppf =
      let open Format in
      function
      | Mul (a, b) -> f ppf "(%a) * (%a)" pp a pp b
      | Div (a, b) -> f ppf "(%a) / (%a)" pp a pp b
      | Not a -> f ppf "not (%a)" pp a
      | Or (a, b) -> f ppf "(%a) || (%a)" pp a pp b
      | Affine a -> f ppf "(%a)" Affine.pp a
      | Eq (a, b) -> f ppf "(%a) == (%a)" pp a pp b
      | If (a, b, c) -> f ppf "(if %a then %a else %a)" pp a pp b pp c

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

    let convert_env =
      Var.Map.map (function
          | Lang.Field f -> f
          | Bool true -> F.one
          | Bool false -> F.zero
          | Pair _ -> assert false)

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
          let b = eval env b in
          let c = eval env c in
          if to_bool a then b else c
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
          Format.ef "eval %a = %a@." Var.pp v pp c;
          let value = eval env c in
          Format.ef "        = %a@." F.pp value;
          if Var.Map.mem v env then assert false;
          let env = Var.Map.add v value env in
          eval_list env codes
  end

  type ty = Field | Bool

  let gen_value ty rng =
    match ty with
    | Field -> F.gen rng
    | Bool -> F.of_int (Gen.int 2 rng)

  module GateM = struct
    let pp_ty ppf ty =
      Format.pp_print_string ppf (match ty with Field -> "field" | Bool -> "bool")

    type state =
      { gates : Gate.Set.t;
        inputs : (Lang.security * ty) Var.Map.t;
        rev_codes : (Var.t * Code.t) list; (* reversed order *)
      }

    let init =
      { gates= Gate.Set.empty;
        inputs= Var.Map.singleton Circuit.one (Lang.Public, Field);
        rev_codes= []
      }

    include StateM

    type 'a t = ('a, state) StateM.t

    let add_gate : Affine.t -> Affine.t -> Affine.t -> unit t = fun lhs l r ->
      fun s ->
        (), { s with gates = Gate.Set.add { lhs; l; r } s.gates }

    let add_input : type a . Var.t -> Lang.security -> a Lang.ty -> unit t = fun v sec ty ->
      fun s ->
        if Var.Map.mem v s.inputs then assert false;
        let ty = match ty with Field -> Field | Bool -> Bool in
        (), { s with inputs = Var.Map.add v (sec, ty) s.inputs }

    let add_code : Var.t -> Code.t -> unit t = fun v e ->
      fun s ->
        if List.mem_assoc v s.rev_codes then assert false;
        (), { s with rev_codes= (v, e) :: s.rev_codes }
  end

  type 'a tree =
    | Leaf of 'a
    | Branch of 'a tree * 'a tree

  let rec compile1 : type a . (Var.t * Affine.t tree) list -> a Lang.t -> Affine.t GateM.t =
    fun env t ->
    let open GateM in
    let+ res = compile env t in
    match res with
    | Leaf af -> af
    | _ -> assert false

  and compile : type a . (Var.t * Affine.t tree) list -> a Lang.t -> Affine.t tree GateM.t =
    let open Lang in
    let open Affine in
    let open Affine.Infix in
    let open GateM in
    let var () =
      let v = var () in
      v, of_var v
    in
    let return1 x = return @@ Leaf x in
    fun env ->
      function
      | Field f -> return1 @@ Affine.of_F f
      | Bool true -> return1 !1
      | Bool false -> return1 !0
      | Input (v, security, ty) ->
          let* () = add_input v security ty in
          return1 @@ of_var v
      | Add (t1, t2) ->
          let* t1 = compile1 env t1 in
          let* t2 = compile1 env t2 in
          return1 @@ t1 + t2
      | Sub (t1, t2) ->
          compile env (Add (t1, Neg t2))
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
               let* () = add_code va Code.S.(!&t1 * !&t2) in
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
               let* () = add_code vc Code.S.(!& !1 / !& b) in
               let* () = add_code vd Code.S.(!&a * !& c) in
               let* () = add_gate !1 b c in
               let* () = add_gate d a c in
               return1 d)
      | Not (Bool b) -> compile env @@ Bool (not b)
      | Not a ->
          (* b
             where
               0 = a * b
               1 = a + b
          *)
          let* a = compile1 env a in
          let vb, b = var () in
          let* () = add_code vb Code.S.(not !&a) in
          let* () = add_gate !0 a b in
          let* () = add_gate !1 (a + b) !1 in
          return1 b
      | And (a, b) -> compile env (Mul (To_field a, To_field b))
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
          let* () = add_code vc Code.S.(!&a || !&b) in
          let* () = add_code vd Code.S.(if_ !&c (!& !1 / !& a_plus_b) !& !0) in
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
          let* b = compile1 env b in
          let* c = compile1 env c in
          (match is_const a with
           | Some a ->
               return1 @@ if F.(a = of_int 1) then b else c
           | None ->
               let vd, d = var () in
               let b_c = b - c in
               match is_const b_c with
               | Some b_c ->
                   return1 @@ c + a *$ b_c
               | None ->
                   let* () = add_code vd Code.S.(!&a * !&b_c) in
                   let* () = add_gate d a b_c in
                   return1 @@ c + d)
      | Eq (a, b) ->
          (* $a == b$

             c where
               1 - c = (a - b) * d
               0 = (a - b) * c
          *)
          let* a = compile env a in
          let* b = compile env b in
          let vc, c = var () in
          let vd, d = var () in
          (* no pair equality yet *)
          let a = match a with Leaf a -> a | _ -> assert false in
          let b = match b with Leaf a -> a | _ -> assert false in
          let* () = add_code vc Code.S.(!&a == !&b) in
          let* () = add_code vd Code.S.(if_ !&c !& !0 (!& !1 / !&(a - b))) in
          let* () = add_gate (!1 - c) (a - b) d in
          let* () = add_gate !0 (a - b) c in
          return1 c
      | To_field t -> compile env t

      | Let (v, a, b) ->
          let* a = compile env a in
          let env = (v, a) :: env in
          compile env b
      | Var v -> return @@ List.assoc v env
      | Pair (a, b) ->
          let* a = compile env a in
          let* b = compile env b in
          return @@ (Branch (a, b) : Affine.t tree)
      | Fst a ->
          let* a = compile env a in
          (match a with
           | Branch (a, _) -> return a
           | _ -> assert false)
      | Snd a ->
          let* a = compile env a in
          (match a with
           | Branch (_, a) -> return a
           | _ -> assert false)

  (* If an output affine is more complex than a variable, add a gate
     to add a variable to alias the affine. *)
  let fix_output : Affine.t -> Affine.t GateM.t = fun a ->
    let open GateM in
    match Var.Map.bindings a (* XXX Affine.bindings or to_list *) with
    | [] -> (* zero *)
        return a
    | [v, _] when v = Circuit.one -> (* constant *)
        return a
    | [_v, f] when F.(f = one) ->
        return a
    | [_] -> (* Weighted variable *)
        (* Weird.  Add another gate for a workaround *)
        let vo = Lang.var () in
        let o = Affine.of_var vo in
        let* () = add_code vo Code.S.(!&a) in
        let* () = add_gate o a (Affine.Infix.(!) 1) in
        return o
    | _ -> (* Affine *)
        let vo = Lang.var () in
        let o = Affine.of_var vo in
        let* () = add_code vo Code.S.(!&a) in
        let* () = add_gate o a (Affine.Infix.(!) 1) in
        return o

  type t =
    { gates : Gate.Set.t;
      inputs : (Lang.security * ty) Var.Map.t;
      mids : Var.Set.t;
      outputs : Var.Set.t;
      codes : (Var.var * Code.code) list
    }

  let rec mapM_tree (f : 'a -> 'b GateM.t) tree =
    let open GateM in
    match tree with
    | Leaf a ->
        let* bt = f a in
        return @@ Leaf bt
    | Branch (a, b) ->
        let* a = mapM_tree f a in
        let+ b = mapM_tree f b in
        Branch (a, b)

  (* Final mending of gates *)
  let compile t =
    let open GateM in
    let* a = compile [] t in
    mapM_tree fix_output a

  let compile t =
    let output, GateM.{ gates; inputs; rev_codes } = compile t GateM.init in
    let outputs =
      let rec f acc = function
        | Branch (a, b) -> f (f acc a) b
        | Leaf a ->
            match Var.Map.bindings a with
            | [v, _] when v <> Circuit.one -> Var.Set.add v acc
            | _ -> assert false
      in
      f Var.Set.empty output
    in
    let mids =
      Var.Set.(diff (Gate.Set.vars gates) (union (Var.Map.domain inputs) outputs))
    in
    output, { gates; inputs; mids; outputs; codes= List.rev rev_codes }

  let rec value_to_tree (v : Lang.value) : F.t tree =
    match v with
    | Field f -> Leaf f
    | Bool true -> Leaf F.one
    | Bool false -> Leaf F.zero
    | Pair (a, b) -> Branch (value_to_tree a, value_to_tree b)

  let test e =
    let open Format in
    ef "code: %a@." Lang.pp e;
    let output, { gates; inputs; outputs; codes; _ }  = compile e in

    ef "public inputs: @[%a@]@."
      (list ",@ " (fun ppf (v, ty) -> f ppf "%a : %a" Var.pp v GateM.pp_ty ty))
    @@ List.filter_map (function (v, (Lang.Public, ty)) -> Some (v, ty) | _ -> None)
    @@ Var.Map.bindings inputs;

    ef "secret inputs: @[%a@]@."
      (list ",@ " (fun ppf (v, ty) -> f ppf "%a : %a" Var.pp v GateM.pp_ty ty))
    @@ List.filter_map (function (v, (Lang.Secret, ty)) -> Some (v, ty) | _ -> None)
    @@ Var.Map.bindings inputs;

    ef "outputs: @[%a@]@."
      (list ",@ " Var.pp)
    @@ Var.Set.elements outputs;

    ef "gates: @[<v>%a@]@." Circuit.Gate.Set.pp gates;

    ef "code: @[<v>%a@]@."
      (list "@," (fun ppf (v, e) -> f ppf "let %a = %a" Var.pp v Code.pp e))
      codes;

    prerr_endline "Lang.eval";
    let inputs =
      let rng = Random.State.make_self_init () in
      Var.Map.mapi (fun v (_, ty) ->
          if v = Circuit.one then Lang.Field F.one
          else
            match ty with
            | Field -> Lang.Field (F.gen rng)
            | Bool -> Lang.Bool (Gen.int 2 rng = 0)) inputs
    in

    let o = value_to_tree @@ Lang.eval inputs e in

    prerr_endline "Code.eval";
    let env =
      Code.eval_list
        (Var.Map.map (fun value ->
             match value with
             | Lang.Field f -> f
             | Bool true -> F.one
             | Bool false -> F.zero
             | Pair _ -> assert false
           ) inputs) codes
    in
    let o' =
      let rec f = function
        | Leaf a -> Leaf (Circuit.Affine.eval env a)
        | Branch (a, b) -> Branch (f a, f b)
      in
      f output
    in
    assert (o = o');

    prerr_endline "test done"
end

let test () =
  let module Comp = Make(Ecp.Bls12_381.Fr) in
  let module Lang = Comp.Lang in
  let open Lang.S in

  Comp.test begin
    let x = Lang.var () in
    let_ x (input secret ty_field) (if_ (var x == !0) !1 !2)
  end;

  Comp.test begin
    let x = Lang.var () in
    let_ x (input secret ty_field) (pair (var x + !1) (var x * !2))
  end
