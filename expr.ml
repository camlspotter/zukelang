open Utils

module Term = struct
  type term = Var of Var.t | Int of int

  type t = term

  let pp ppf = function
    | Var s -> Var.pp ppf s
    | Int i -> Format.int ppf i
end

module Expr = struct
  type binop = Add | Mul

  type expr = Term of Term.t | BinApp of binop * expr * expr

  type t = expr

  let rec pp ppf = function
    | Term t -> Term.pp ppf t
    | BinApp (Add, t1, t2) -> Format.fprintf ppf "(%a + %a)" pp t1 pp t2
    | BinApp (Mul, t1, t2) -> Format.fprintf ppf "(%a * %a)" pp t1 pp t2

  let var s = Term (Term.Var (Var.of_string s))

  let int n = Term (Term.Int n)

  let mul x y = BinApp (Mul, x, y)

  let add x y = BinApp (Add, x, y)

  let rec eval env = function
    | Term (Int n) -> n
    | Term (Var x) -> (
        match List.assoc_opt x env with None -> raise Not_found | Some n -> n)
    | BinApp (Add, t1, t2) ->
        let n1 = eval env t1 in
        let n2 = eval env t2 in
        n1 + n2
    | BinApp (Mul, t1, t2) ->
        let n1 = eval env t1 in
        let n2 = eval env t2 in
        n1 * n2

  module Infix = struct
    let (+) = add
    let ( * ) = mul
    let (!!) = int
    let (??) = var
  end

end

module Flatten = struct
  (** Looks like three-address code *)
  type flatten = Var.t * Expr.binop * Term.t * Term.t

  type t = flatten

  let pp ppf ((v, binop, t1, t2) : t) =
    Format.fprintf
      ppf
      "%a = %a %s %a"
      Var.pp v
      Term.pp t1
      (match binop with Expr.Add -> "+" | Mul -> "*")
      Term.pp t2

  let flatten (v, expr) : t list =
    let cntr = ref 0 in
    let mk_mid_var () =
      incr cntr ;
      Var.of_string @@ Printf.sprintf "_sym%d" !cntr
    in
    let rec loop = function
      | _v, Expr.Term _ -> assert false
      | v, BinApp (binop, e1, e2) ->
          let t1, fs1 = loop' e1 in
          let t2, fs2 = loop' e2 in
          ((v, binop, t1, t2) :: fs1) @ fs2
    and loop' e =
      match e with
      | Term t -> (t, [])
      | e ->
          let v = mk_mid_var () in
          (Term.Var v, loop (v, e))
    in
    loop (v, expr)

  let vars' acc (v1, _, t2, t3) =
    let do_t t acc =
      match t with Term.Int _ -> acc | Var v -> Var.Set.add v acc
    in
    do_t (Var v1) @@ do_t t2 @@ do_t t3 acc

  let vars fs = List.fold_left (fun acc f -> vars' acc f) Var.Set.empty fs

  let eval_ env (op, t1, t2) =
    let eval_t t =
      match t with
      | Term.Int i -> Some i
      | Term.Var v -> (
          match List.assoc_opt v env with None -> None | Some i -> Some i)
    in
    match (op, eval_t t1, eval_t t2) with
    | Expr.Add, Some i1, Some i2 -> Some (i1 + i2)
    | Expr.Mul, Some i1, Some i2 -> Some (i1 * i2)
    | _ -> None

  let eval env fs =
    let vars = vars fs in
    let unks =
      List.fold_left (fun acc (v, _) -> Var.Set.remove v acc) vars env
    in
    let rec loop sol unks rev_fs fs =
      if Var.Set.is_empty unks then sol
      else
        match fs with
        | [] -> assert false
        | ((v, op, t1, t2) as f) :: fs -> (
            match eval_ sol (op, t1, t2) with
            | Some i ->
                loop
                  ((v, i) :: sol)
                  (Var.Set.remove v unks)
                  []
                  (List.rev_append rev_fs fs)
            | None -> loop sol unks (f :: rev_fs) fs)
    in
    loop env unks [] fs
end
