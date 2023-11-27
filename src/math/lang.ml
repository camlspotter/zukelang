open Misclib

let var =
  let cntr = ref 0 in
  fun () ->
    incr cntr;
    Var.of_string (Printf.sprintf "v%d" !cntr)

module Make(F : Field.COMPARABLE) = struct

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
    | Input : Var.t * security * 'a ty -> 'a t
    | Not : bool t -> bool t
    | And : bool t * bool t -> bool t
    | Or : bool t * bool t -> bool t
    | If : bool t * 'a t * 'a t -> 'a t
    | Eq : 'a t * 'a t -> bool t
    | To_field : _ t -> F.t t (* cast *)
    | Let : Var.t * 'a t * 'b t -> 'b t
    | Var : Var.t -> 'a t
    | Neg : F.t t -> F.t t
    | Pair : 'a t * 'b t -> ('a * 'b) t
    | Fst : ('a * 'b) t -> 'a t
    | Snd : ('a * 'b) t -> 'b t
    | Left : 'a t -> ('a, _) Either.t t
    | Right : 'b t -> (_, 'b) Either.t t
    | Case : ('a, 'b) Either.t t * ('a t -> 'c t) * ('b t -> 'c t) -> 'c t

  let ptree e =
    let var =
      let cntr = ref 0 in
      fun () ->
        incr cntr;
        Var.of_string (Printf.sprintf "c%d" !cntr)
    in
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
      | Input (v, Public, _) ->
          [%expr ([%e Exp.ident { txt= Longident.Lident (Var.to_string v); loc= Location.none }] : public)]
      | Input (v, Secret, _) ->
          [%expr ([%e Exp.ident { txt= Longident.Lident (Var.to_string v); loc= Location.none }] : secret)]
      | Var v -> Exp.ident { txt= Longident.Lident (Var.to_string v); loc= Location.none }
      | Not b -> [%expr not [%e ptree b]]
      | And (t1, t2) -> [%expr [%e ptree t1] && [%e ptree t2]]
      | Or (t1, t2) -> [%expr [%e ptree t1] || [%e ptree t2]]
      | If (t1, t2, t3) -> [%expr if [%e ptree t1] then [%e ptree t2] else [%e ptree t3]]
      | Eq (t1, t2) -> [%expr [%e ptree t1] == [%e ptree t2]]
      | To_field t -> [%expr to_field [%e ptree t]]
      | Let (v, t1, t2) -> [%expr let [%p Pat.var {txt= Var.to_string v; loc= Location.none}] = [%e ptree t1] in [%e ptree t2]]
      | Neg t -> [%expr ~- [%e ptree t]]
      | Pair (a, b) -> [%expr ([%e ptree a], [%e ptree b])]
      | Fst a -> [%expr fst [%e ptree a]]
      | Snd a -> [%expr snd [%e ptree a]]
      | Left a -> [%expr Left [%e ptree a]]
      | Right a -> [%expr Right [%e ptree a]]
      | Case (ab, a, b) ->
          let va = var () in
          let vb = var () in
          [%expr
            match [%e ptree ab] with
            | Left [%p Pat.var {txt= Var.to_string va; loc= Location.none}] -> [%e ptree (a (Var va))]
            | Right [%p Pat.var {txt= Var.to_string vb; loc= Location.none}] -> [%e ptree (b (Var vb))]]
    in
    ptree e

  let pp ppf t = Ppxlib_ast.Pprintast.expression ppf @@ ptree t

  let var = var

  module S = struct

    let ty_field : _ ty = Field
    let ty_bool : _ ty = Bool

    let public = Public
    let secret = Secret

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

      let (~-) a =
      match a with
      | Field a -> Field F.(~- a)
      | _ -> Neg a

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

    let input sec ty =
      let v = var () in
      Input (v, sec, ty)

    let to_field : type a. a t -> F.t t = fun t ->
      match t with
      | Field _ -> t
      | _ -> To_field t

    let var v = Var v

    let let_ v a b = Let (v, a, b)

    let (==) a b = Eq (a, b)

    let pair a b = Pair (a, b)

    let fst a = Fst a

    let snd a = Snd a

    let left a = Left a

    let right a = Right a

    let case ab a b = Case (ab, a, b)
  end

  type value =
    | Field of F.t
    | Bool of bool
    | Pair of value * value
    | Left of value
    | Right of value

  type env = value Var.Map.t

  let field = function
    | Field f -> f
    | _ -> assert false

  let bool = function
    | Bool b -> b
    | _ -> assert false

  let eval env e =
    let var = Var.generator "eval" in
    let rec eval : type a . env -> a t -> value = fun env e ->
      match e with
      | Input (v, _sec, _ty) -> Var.Map.find v env
      | Field f -> Field f
      | Bool b -> Bool b
      | Add (a, b) ->
          let a = field @@ eval env a in
          let b = field @@ eval env b in
          Field F.(a + b)
      | Sub (a, b) ->
          let a = field @@ eval env a in
          let b = field @@ eval env b in
          Field F.(a - b)
      | Mul (a, b) ->
          let a = field @@ eval env a in
          let b = field @@ eval env b in
          Field F.(a * b)
      | Div (a, b) ->
          let a = field @@ eval env a in
          let b = field @@ eval env b in
          Field F.(a / b)
      | Not a ->
          let a = bool @@ eval env a in
          Bool (not a)
      | And (a, b) ->
          let a = bool @@ eval env a in
          let b = bool @@ eval env b in
          Bool (a && b)
      | Or (a, b) ->
          let a = bool @@ eval env a in
          let b = bool @@ eval env b in
          Bool (a || b)
      | If (a, b, c) ->
          let a = bool @@ eval env a in
          if a then eval env b else eval env c
      | Eq (a, b) ->
          let a = eval env a in
          let b = eval env b in
          Bool (a = b)
      | To_field a ->
          (match eval env a with
           | Field f -> Field f
           | Bool true -> Field F.one
           | Bool false -> Field F.zero
           | Pair _ | Left _ | Right _ -> assert false)
      | Let (v, a, b) ->
          let a = eval env a in
          eval (Var.Map.add v a env) b
      | Var v ->
          Var.Map.find v env
      | Neg a ->
          let a = bool @@ eval env a in
          Bool (not a)
      | Pair (a, b) ->
          let a = eval env a in
          let b = eval env b in
          Pair (a, b)
      | Fst a ->
          (match eval env a with
           | Pair (a, _) -> a
           | _ -> assert false)
      | Snd a ->
          (match eval env a with
           | Pair (_, b) -> b
           | _ -> assert false)
      | Left a -> Left (eval env a)
      | Right a -> Right (eval env a)
      | Case (ab, a, b) ->
          (match eval env ab with
           | Left x ->
               let v = var () in
               eval (Var.Map.add v x env) @@ a (Var v)
           | Right x ->
               let v = var () in
               eval (Var.Map.add v x env) @@ b (Var v)
           | _ -> assert false)
    in
    eval env e
end
