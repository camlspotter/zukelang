(* https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649 *)

open Utils
open Expr

type row = (Var.t * int) list

type elem = row Abc.t

type t = row list Abc.t

let mul_row_vec row vec =
  List.fold_left
    (fun acc (v, a) ->
      match List.assoc_opt v vec with
      | None ->
          prerr_endline ("Not_found: " ^ Var.to_string v) ;
          assert false
      | Some b -> (a * b) + acc)
    0
    row

let check_elem Abc.{a; b; c} vec =
  assert (mul_row_vec a vec * mul_row_vec b vec = mul_row_vec c vec)

let check Abc.{a=aa; b=bb; c=cc} vec =
  let rec loop aa bb cc =
    match (aa, bb, cc) with
    | [], [], [] -> ()
    | a :: aa, b :: bb, c :: cc ->
        check_elem {a; b; c} vec ;
        loop aa bb cc
    | _ -> assert false
  in
  loop aa bb cc

let pp_row ppf row =
  let open Format in
  fprintf ppf "@[" ;
  pp_print_list
    ~pp_sep:(pp_list_sep ";@ ")
    (fun ppf (v, i) -> fprintf ppf "%a = %d" Var.pp v i)
    ppf
    row ;
  fprintf ppf "@]"

let pp_elem = Abc.pp pp_row

let pp =
  let open Format in
  Abc.pp (pp_print_list ~pp_sep:(pp_list_sep ";@ ") pp_row)

let one = Var.of_string "~one"

let of_term = function Term.Var v -> [(v, 1)] | Int n -> [(one, n)]

let add vis1 vis2 =
  let vs = List.sort_uniq compare @@ List.map fst vis1 @ List.map fst vis2 in
  let find v vis = Option.value ~default:0 (List.assoc_opt v vis) in
  List.map (fun v -> (v, find v vis1 + find v vis2)) vs

let of_flatten (v0, binop, t1, t2) =
  let open Abc in
  match binop with
  | Expr.Mul ->
      let a = of_term t1 in
      let b = of_term t2 in
      let c = of_term (Term.Var v0) in
      {a; b; c}
  | Expr.Add ->
      let a = add (of_term t1) (of_term t2) in
      let b = [(one, 1)] in
      let c = of_term (Term.Var v0) in
      {a; b; c}

let normalize vars t =
  let vars = one :: vars in
  List.map (fun v -> (v, Option.value ~default:0 (List.assoc_opt v t))) vars

let of_flatten vars f =
  let open Abc in
  let {a; b; c} = of_flatten f in
  let a = normalize vars a in
  let b = normalize vars b in
  let c = normalize vars c in
  {a; b; c}

let of_flatten_list vars fs =
  let open Abc in
  let elems = List.map (of_flatten vars) fs in
  let aa = List.map (fun elem -> elem.a) elems in
  let bb = List.map (fun elem -> elem.b) elems in
  let cc = List.map (fun elem -> elem.c) elems in
  {a=aa; b=bb; c=cc}

let transpose (rows : row list) =
  let rec loop rows =
    match rows with
    | [row] -> List.map (fun (s, n) -> (s, [n])) row
    | row :: rows ->
        let cols = loop rows in
        List.map2
          (fun (n, x) (n', xs) ->
            assert (n = n') ;
            (n, x :: xs))
          row
          cols
    | [] -> assert false
  in
  loop rows
