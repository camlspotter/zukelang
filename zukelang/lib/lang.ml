open Utils

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
    | Neg : F.t t -> F.t t
    | Assert : F.t t * F.t t * 'a t -> 'a t

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
    | Neg t -> [%expr ~- [%e ptree t]]
    | Assert (t1, t2, t3) -> [%expr assert ([%e ptree t1] = [%e ptree t2]); [%e ptree t3]]

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

    let input sec ty = Input (sec, ty)

    let to_field : type a. a t -> F.t t = fun t ->
      match t with
      | Field _ -> t
      | _ -> To_field t

    let var v = Var v

    let let_ v a b = Let (v, a, b)

    let (==) a b = Eq (a, b)

    let cast a = Cast a

    let assert_ (a, b) c = Assert (a, b, c)

    let rec in_let t f =
      match t with
      | Let (v, t1, t2) -> Let (v, t1, in_let t2 f)
      | t -> f t

    let in_let2 t1 t2 f = in_let t1 (fun t1 -> in_let t2 (fun t2 -> f t1 t2))
  end

end
