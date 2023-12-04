open Misclib

module Make(F : Curve.F) = struct

  module Root = Curve.Root_of_unity(F)

  let f_of_uint32 i =
    match Root.f_of_uint 32 i with
    | None -> invalid_arg "This field does not support uint32"
    | Some x -> x

  let () =
    let open Format in
    ef "ROOT@.";
    ef "0u = %a@." F.pp @@ f_of_uint32 0;
    ef "1u = %a@." F.pp @@ f_of_uint32 1;
    ef "(2^32-1)u = %a@." F.pp @@ f_of_uint32 (1 lsl 32 - 1);
    ef "(2^32)u = %a@." F.pp @@ f_of_uint32 (1 lsl 32);
    (* $g^a + g^b = g^{a+b}$ *)
    assert F.(f_of_uint32 5 * f_of_uint32 7 = f_of_uint32 12);
    ef "5u + 7u = 12u@."

  type security = Public | Secret

  let pp_security ppf s =
    Format.string ppf (match s with Public -> "public" | Secret -> "secret")

  module Type = struct
    type uint32

    type _ t =
      | Field : F.t t
      | Bool : bool t
      | Uint32 : uint32 t
      | Pair : 'a t * 'b t -> ('a * 'b) t
      | Either : 'a t * 'b t -> ('a, 'b) Either.t t

    type packed = Packed : _ t -> packed

    let rec equal : type a b . a t -> b t -> (a, b) GADT.eq option = fun a b ->
      let open GADT in
      match a, b with
      | Field, Field -> Some Refl
      | Bool, Bool -> Some Refl
      | Uint32, Uint32 -> Some Refl
      | Pair (t11, t12), Pair (t21, t22) ->
          (match equal t11 t21 with
           | None -> None
           | Some Refl ->
               match equal t12 t22 with
               | None -> None
               | Some Refl -> Some Refl)
      | Either (t11, t12), Either (t21, t22) ->
          (match equal t11 t21 with
           | None -> None
           | Some Refl ->
               match equal t12 t22 with
               | None -> None
               | Some Refl -> Some Refl)
      | _ -> None

    let rec pp : type a. a t printer = fun ppf ->
      let open Format in
      function
      | Field -> string ppf "field"
      | Bool -> string ppf "bool"
      | Uint32 -> string ppf "uint32"
      | Pair (ty1, ty2) -> f ppf "(%a * %a)" pp ty1 pp ty2
      | Either (ty1, ty2) -> f ppf "(%a, %a) Either.t" pp ty1 pp ty2
  end

  module Expr = struct
    (** Type of ZK computation *)
    type 'a t =
      { desc : 'a desc;
        ty : 'a Type.t
      }

    and 'a desc =
      | Field : F.t -> F.t desc
      | Bool : bool -> bool desc
      | Uint32 : int -> Type.uint32 desc
      | Add : F.t t * F.t t -> F.t desc
      | Sub : F.t t * F.t t -> F.t desc
      | Mul : F.t t * F.t t -> F.t desc
      | Div : F.t t * F.t t -> F.t desc
      | Input : string * security -> 'a desc
      | Not : bool t -> bool desc
      | And : bool t * bool t -> bool desc
      | Or : bool t * bool t -> bool desc
      | If : bool t * 'a t * 'a t -> 'a desc
      | Eq : 'a t * 'a t -> bool desc
      | To_field : _ t -> F.t desc (* cast *)
      | Let : Var.t * 'a t * 'b t -> 'b desc
      | Var : Var.t -> 'a desc
      | Neg : F.t t -> F.t desc
      | Pair : 'a t * 'b t -> ('a * 'b) desc
      | Fst : ('a * 'b) t -> 'a desc
      | Snd : ('a * 'b) t -> 'b desc
      | Left : 'a t -> ('a, _) Either.t desc
      | Right : 'b t -> (_, 'b) Either.t desc
      | Case : ('a, 'b) Either.t t * Var.t * 'c t * Var.t * 'c t -> 'c desc
      | Add_uint32 : Type.uint32 t * Type.uint32 t -> Type.uint32 desc
      | Sub_uint32 : Type.uint32 t * Type.uint32 t -> Type.uint32 desc

    let ptree e =
      let rec ptree : type a. a t -> Ptree.t = fun e ->
        let loc = Location.none in
        match e.desc with
        | Field f -> Ptree.int @@ Format.asprintf "%a" F.pp f
        | Uint32 i -> Ptree.int ~suffix:'u' @@ string_of_int i
        | Bool true -> [%expr true]
        | Bool false -> [%expr false]
        | Add (t1, t2) -> [%expr [%e ptree t1] + [%e ptree t2]]
        | Sub (t1, t2) -> [%expr [%e ptree t1] - [%e ptree t2]]
        | Mul (t1, t2) -> [%expr [%e ptree t1] * [%e ptree t2]]
        | Div (t1, t2) -> [%expr [%e ptree t1] / [%e ptree t2]]
        | Input (name, Public) ->
            [%expr (input [%e Ptree.string name] : public)]
        | Input (name, Secret) ->
            [%expr (input [%e Ptree.string name] : secret)]
        | Var v -> Ptree.var (Var.to_string v)
        | Not b -> [%expr not [%e ptree b]]
        | And (t1, t2) -> [%expr [%e ptree t1] && [%e ptree t2]]
        | Or (t1, t2) -> [%expr [%e ptree t1] || [%e ptree t2]]
        | If (t1, t2, t3) -> [%expr if [%e ptree t1] then [%e ptree t2] else [%e ptree t3]]
        | Eq (t1, t2) -> [%expr [%e ptree t1] == [%e ptree t2]]
        | To_field t -> [%expr to_field [%e ptree t]]
        | Let (v, t1, t2) ->
            [%expr let [%p Ptree.pvar @@ Var.to_string v] = [%e ptree t1] in [%e ptree t2]]
        | Neg t -> [%expr ~- [%e ptree t]]
        | Pair (a, b) -> [%expr ([%e ptree a], [%e ptree b])]
        | Fst a -> [%expr fst [%e ptree a]]
        | Snd a -> [%expr snd [%e ptree a]]
        | Left a -> [%expr Left [%e ptree a]]
        | Right a -> [%expr Right [%e ptree a]]
        | Case (ab, va, a, vb, b) ->
            [%expr
              match [%e ptree ab] with
              | Left [%p Ptree.pvar @@ Var.to_string va] -> [%e ptree a]
              | Right [%p Ptree.pvar @@ Var.to_string vb] -> [%e ptree b]]
        | Add_uint32 (t1, t2) -> [%expr [%e ptree t1] + [%e ptree t2]]
        | Sub_uint32 (t1, t2) -> [%expr [%e ptree t1] - [%e ptree t2]]
      in
      ptree e

    let pp ppf t = Ptree.pp ppf @@ ptree t

    module Combinator = struct
      let ty_field : _ Type.t = Field

      let ty_bool : _ Type.t = Bool

      let ty_uint32 : _ Type.t = Uint32

      let ty_pair t1 t2 : _ Type.t = Pair (t1, t2)
      let ( *: ) = ty_pair

      let ty_either t1 t2 : _ Type.t = Either (t1, t2)
      let ( +: ) = ty_either

      let public = Public
      let secret = Secret

      let mk desc ty = { desc; ty }

      let bool b = mk (Bool b) ty_bool

      let field n = mk (Field n) ty_field

      let uint32 n = mk (Uint32 n) ty_uint32 (* range check? *)

      let (!) n = mk (Field (F.of_int n)) ty_field

      let (+) a b = mk (Add (a, b)) ty_field

      let (-) a b = mk (Sub (a, b)) ty_field

      let (~-) a = mk (Neg a) ty_field

      let ( * ) a b = mk (Mul (a, b)) ty_field

      let (/) a b = mk (Div (a, b)) ty_field

      let not a = mk (Not a) ty_bool

      let (&&) a b = mk (And (a, b)) ty_bool

      let (||) a b = mk (Or (a, b)) ty_bool

      let if_ a b c = mk (If (a, b, c)) b.ty

      let input name sec ty = mk (Input (name, sec)) ty

      let to_field : type a. a t -> F.t t = fun t ->
        match t.ty with
        | Field | Bool | Uint32 -> mk (To_field t) ty_field
        | _ -> invalid_arg "to_field"

      let var v ty = mk (Var v) ty

      let let_ a b =
        let v = Var.make "x" in
        let b = b (var v a.ty) in
        mk (Let (v, a, b)) b.ty

      let (==) a b = mk (Eq (a, b)) ty_bool

      let pair a b = mk (Pair (a, b)) @@ ty_pair a.ty b.ty

      let fst a =
        let ty = match a.ty with
          | Pair (ty, _) -> ty
          | _ -> assert false
        in
        mk (Fst a) ty

      let snd a =
        let ty = match a.ty with
          | Pair (_, ty) -> ty
          | _ -> assert false
        in
        mk (Snd a) ty

      let left a bty = mk (Left a) @@ ty_either a.ty bty

      let right aty b = mk (Right b) @@ ty_either aty b.ty

      let case ab fa fb =
        match ab.ty with
        | Either (aty, bty) ->
            let va = Var.make "case" in
            let vb = Var.make "case" in
            let a = fa (var va aty) in
            let b = fb (var vb bty) in
            mk (Case (ab, va, a, vb, b)) a.ty
        | _ -> assert false

      module Uint32 = struct
        let (+) a b = mk (Add_uint32 (a, b)) ty_uint32
        let (-) a b = mk (Sub_uint32 (a, b)) ty_uint32
      end
    end
  end

  module Value = struct
    type _ t =
      | Field : F.t -> F.t t
      | Bool : bool -> bool t
      | Uint32 : int -> Type.uint32 t
      | Pair : 'a t * 'b t -> ('a * 'b) t
      | Left : 'a t -> ('a, _) Either.t t
      | Right : 'b t -> (_, 'b) Either.t t

    type packed = Packed : 'a t * 'a Type.t -> packed

    let unpack : type a. a Type.t -> packed -> a t option =
      fun ty (Packed (t, ty')) ->
      match Type.equal ty ty' with
      | Some GADT.Refl -> Some t
      | None -> None

    let rec gen : type a. a Type.t -> a t Gen.t = fun ty ->
      let open Gen.Syntax in
      match ty with
      | Field -> let+ f = F.gen in Field f
      | Bool -> let+ b = Gen.bool in Bool b
      | Uint32 -> let+ i = Gen.uint32 in Uint32 i
      | Pair (ty1, ty2) ->
          let* t1 = gen ty1 in
          let+ t2 = gen ty2 in
          Pair (t1, t2)
      | Either (ty1, ty2) ->
          let* b = Gen.bool in
          match b with
          | true ->
              let+ t1 = gen ty1 in
              Left t1
          | false ->
              let+ t2 = gen ty2 in
              Right t2

    let ptree v =
      let rec ptree : type a. a t -> Ptree.t = fun v ->
        let loc = Location.none in
        match v with
        | Field f -> Ptree.int @@ Format.asprintf "%a" F.pp f
        | Bool true -> [%expr true]
        | Bool false -> [%expr false]
        | Uint32 i -> Ptree.int ~suffix:'u' @@ string_of_int i
        | Pair (a, b) -> [%expr ([%e ptree a], [%e ptree b])]
        | Left a -> [%expr Left [%e ptree a]]
        | Right a -> [%expr Right [%e ptree a]]
      in
      ptree v

    let pp ppf t = Ptree.pp ppf @@ ptree t
  end

  module Env = struct
    type t = Value.packed Var.Map.t

    let add v ty value map = Var.Map.add v (Value.Packed (value, ty)) map

    let find v ty env =
      match Value.unpack ty (Var.Map.find v env) with
      | Some v -> v
      | None -> invalid_arg "ill typed"
  end

  module Eval = struct
    let eval inputs e =
      let rec eval : type a . Env.t -> a Expr.t -> a Value.t =
        fun env e ->
          let open Expr in
          let field = function
            | Value.Field f -> f
            | _ -> assert false
          in
          let bool = function
            | Value.Bool b -> b
            | _ -> assert false
          in
          match e.desc with
          | Input (name, _sec) ->
              Option.get @@ Value.unpack e.ty @@ String.Map.find name inputs
          | Field f -> Field f
          | Uint32 i -> Uint32 i
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
              (* XXX To_field forces Lang have some compilation semantics. *)
              (match eval env a with
               | Field f -> Field f
               | Bool true -> Field F.one
               | Bool false -> Field F.zero
               | Uint32 i -> Field (f_of_uint32 i)
               | Pair _ | Left _ | Right _ -> assert false)
          | Let (v, a, b) ->
              eval (Env.add v a.ty (eval env a) env) b
          | Var v ->
              Env.find v e.ty env
          | Neg a ->
              let f = field @@ eval env a in
              Field F.(~- f)
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
          | Case (ab, va, a, vb, b) ->
              (match ab.ty with
               | Either (aty, bty) ->
                   (match eval env ab with
                    | Left x -> eval (Env.add va aty x env) a
                    | Right x -> eval (Env.add vb bty x env) b
                    | _ -> assert false)
               | _ -> assert false)
          | Add_uint32 (a, b) ->
              let a = eval env a in
              let b = eval env b in
              (match a, b with
              | Uint32 a, Uint32 b ->
                  let c = a + b in
                  Uint32 (if c >= 1 lsl 32 then c - 1 lsl 32 else c)
              | _ -> assert false)
          | Sub_uint32 (a, b) ->
              let a = eval env a in
              let b = eval env b in
              (match a, b with
              | Uint32 a, Uint32 b ->
                  let c = a - b in
                  Uint32 (if c < 0 then c + 1 lsl 32 else c)
              | _ -> assert false)
      in
      eval Var.Map.empty e
  end
end
