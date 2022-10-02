open Utils

module VarSet = Set.Make(struct type t = string let compare (x : string) y = compare x y end)

module Term = struct
  type var = string

  type t =
    | Var of var
    | Int of int

  let pp_var ppf s = Format.pp_print_string ppf s

  let pp ppf = function
    | Var s -> pp_var ppf s
    | Int i -> Format.fprintf ppf "%d" i
end

module Expr = struct
  type binop =
    | Add
    | Mul

  type t =
    | Term of Term.t
    | BinApp of binop * t * t

  let rec pp ppf = function
    | Term t -> Term.pp ppf t
    | BinApp (Add, t1, t2) -> Format.fprintf ppf "(%a + %a)" pp t1 pp t2
    | BinApp (Mul, t1, t2) -> Format.fprintf ppf "(%a * %a)" pp t1 pp t2

  let var s = Term (Term.Var s)
  let int n = Term (Term.Int n)
  let mul x y = BinApp (Mul, x, y)
  let add x y = BinApp (Add, x, y)

  let rec eval env = function
    | Term (Int n) -> n
    | Term (Var x) ->
        begin match List.assoc_opt x env with
          | None -> raise Not_found
          | Some n -> n
        end
    | BinApp (Add, t1, t2) ->
        let n1 = eval env t1 in
        let n2 = eval env t2 in
        n1 + n2
    | BinApp (Mul, t1, t2) ->
        let n1 = eval env t1 in
        let n2 = eval env t2 in
        n1 * n2
end

module Flatten = struct
  (** Looks like three-address code *)
  type t = Term.var * Expr.binop * Term.t * Term.t

  let pp ppf (v, binop, t1, t2 : t) =
    Format.fprintf ppf "%a = %a %s %a"
      Term.pp_var v
      Term.pp t1
      (match binop with Expr.Add -> "+" | Mul -> "*")
      Term.pp t2

  let flatten (v, expr) : t list =
    let cntr = ref 0 in
    let mkvar () = incr cntr; Printf.sprintf "sym%d" !cntr in
    let rec loop = function
      | _v, Expr.Term _ -> assert false
      | v, BinApp (binop, e1, e2) ->
          let t1, fs1 = loop' e1 in
          let t2, fs2 = loop' e2 in
          (v, binop, t1, t2) :: fs1 @ fs2
    and loop' e =
      match e with
      | Term t -> t, []
      | e ->
          let v = mkvar () in
          Term.Var v, loop (v, e)
    in
    loop (v, expr)

  let vars' acc (v1, _, t2, t3) =
    let do_t t acc = match t with
      | Term.Int _ -> acc
      | Var v -> VarSet.add v acc
    in
    do_t (Var v1) @@ do_t t2 @@ do_t t3 acc

  let vars fs =
    List.fold_left (fun acc f -> vars' acc f) VarSet.empty fs

  let eval_ env (op, t1, t2) =
    let eval_t t =
      match t with
      | Term.Int i -> Some i
      | Term.Var v ->
          match List.assoc_opt v env with
          | None -> None
          | Some i -> Some i
    in
    match op, eval_t t1, eval_t t2 with
    | Expr.Add, Some i1, Some i2 -> Some (i1 + i2)
    | Expr.Mul, Some i1, Some i2 -> Some (i1 * i2)
    | _ -> None

  let eval env fs =
    let vars = vars fs in
    let unks =
      List.fold_left (fun acc (v,_) ->
          VarSet.remove v acc) vars env
    in
    let rec loop sol unks rev_fs fs =
      if VarSet.is_empty unks then sol
      else
        match fs with
        | [] -> assert false
        | (v, op, t1, t2 as f)::fs ->
            match eval_ sol (op, t1, t2) with
            | Some i ->
                loop ((v,i) :: sol) (VarSet.remove v unks) [] (List.rev_append rev_fs fs)
            | None ->
                loop sol unks (f::rev_fs) fs
    in
    loop env unks [] fs
end

module R1CS = struct
  type row = (Term.var * int) list
  type elem = { a : row; b : row; c : row }
  type t = { aa : row list; bb : row list; cc : row list }

  let mul_row_vec row vec =
    List.fold_left (fun acc (v, a) ->
        match List.assoc_opt v vec with
        | None ->
            prerr_endline ("Not_found: " ^ v);
            assert false
        | Some b -> a * b + acc) 0 row

  let check_elem {a; b; c} vec =
    assert (mul_row_vec a vec * mul_row_vec b vec = mul_row_vec c vec)

  let check {aa; bb; cc} vec =
    let rec loop aa bb cc =
      match aa, bb, cc with
      | [], [], [] -> ()
      | a::aa, b::bb, c::cc ->
          check_elem {a; b; c} vec;
          loop aa bb cc
      | _ -> assert false
    in
    loop aa bb cc

  let pp_row ppf row =
    let open Format in
    fprintf ppf "@[";
    pp_print_list ~pp_sep:(pp_list_sep ";@ ")
      (fun ppf (v, i) -> fprintf ppf "%a = %d" Term.pp_var v i)
      ppf row;
    fprintf ppf "@]"

  let pp_elem ppf {a;b;c} =
    let open Format in
    fprintf ppf "@[";
    fprintf ppf "a: @[<h>%a@];@ " pp_row a;
    fprintf ppf "b: @[<h>%a@];@ " pp_row b;
    fprintf ppf "c: @[<h>%a@];@ " pp_row c;
    fprintf ppf "@]"

  let pp ppf {aa;bb;cc} =
    let open Format in
    fprintf ppf "A: @[<v>%a@];@." (pp_print_list ~pp_sep:(pp_list_sep ";@ ") pp_row) aa;
    fprintf ppf "B: @[<v>%a@];@." (pp_print_list ~pp_sep:(pp_list_sep ";@ ") pp_row) bb;
    fprintf ppf "C: @[<v>%a@];@." (pp_print_list ~pp_sep:(pp_list_sep ";@ ") pp_row) cc

  let one = "~one"

  let of_term = function
    | Term.Var v -> [v, 1]
    | Term.Int n -> [one, n]

  let add vis1 vis2 =
    let vs = List.sort_uniq compare @@ List.map fst vis1 @ List.map fst vis2 in
    let find v vis = Option.value ~default:0 (List.assoc_opt v vis) in
    List.map (fun v -> (v, find v vis1 + find v vis2)) vs

  let of_flatten (v0, binop, t1, t2) =
    match binop with
    | Expr.Mul ->
        let a = of_term t1 in
        let b = of_term t2 in
        let c = of_term (Term.Var v0) in
        {a;b;c}
    | Expr.Add ->
        let a = add (of_term t1) (of_term t2) in
        let b = [one, 1] in
        let c = of_term (Term.Var v0) in
        {a;b;c}

  let normalize vars t =
    let vars = one :: vars in
    List.map (fun v ->
        v, Option.value ~default:0 (List.assoc_opt v t)) vars

  let of_flatten vars f =
    let {a;b;c} = of_flatten f in
    let a = normalize vars a in
    let b = normalize vars b in
    let c = normalize vars c in
    {a;b;c}

  let of_flatten_list vars fs =
    let elems = List.map (of_flatten vars) fs in
    let aa = List.map (fun elem -> elem.a) elems in
    let bb = List.map (fun elem -> elem.b) elems in
    let cc = List.map (fun elem -> elem.c) elems in
    {aa; bb; cc}

  let transpose (rows : row list) =
    let rec loop rows =
      match rows with
      | [row] -> List.map (fun (s,n) -> s,[n]) row
      | row::rows ->
          let cols = loop rows in
          List.map2 (fun (n,x) (n', xs) ->
              assert (n = n');
              n, x::xs) row cols
      | [] -> assert false
    in
    loop rows
end

module PQ = Polynomial.Make(Polynomial.Q)

module QAP = struct
  let of_R1CS_rows rows =
    let trans = R1CS.transpose rows in
(*
    List.iter (fun (n, xs) ->
        Format.(eprintf "@[%s: %a@]@."
                  n
                  (pp_print_list ~pp_sep:(pp_list_sep ";@ ") pp_print_int) xs))
      trans;
*)
    let ps =
      List.map (fun (n,xs) ->
          let xs = List.rev xs in
          let xys = List.mapi (fun i x -> (Q.of_int (i+1), Q.of_int x)) xs in
          n, PQ.interporate xys) trans
    in
(*
    List.iter (fun (n,p) -> Format.eprintf "%s: %a@." n PQ.pp p) ps;
*)
    ps

  let of_R1CS {R1CS.aa; bb; cc} =
    of_R1CS_rows aa,
    of_R1CS_rows bb,
    of_R1CS_rows cc
end

let () =
  let rhs = let open Expr in add (add (mul (mul (var "x") (var "x")) (var "x")) (var "x")) (int 5) in
  assert (Expr.eval [("x", 3)] rhs = 35);
  let lhs = "~out" in
  Format.eprintf "%a = %a@." Term.pp_var lhs Expr.pp rhs;

  prerr_endline "*** flatten";
  let fs = Flatten.flatten (lhs, rhs) in
  List.iter (fun eq -> Format.eprintf "%a@." Flatten.pp eq) fs;

  prerr_endline "*** solution vector";
  let sol = Flatten.eval [("x",3)] fs in
  List.iter (fun (v,n) -> Format.eprintf "%a : %d@." Term.pp_var v n) sol;
  let sol = ("~one", 1) :: sol in

  prerr_endline "*** R1CS elems";
  let vars = List.of_seq @@ VarSet.to_seq @@ Flatten.vars fs in
  List.iter (fun f ->
      let res = R1CS.of_flatten vars f in
      Format.eprintf "%a@." Flatten.pp f;
      Format.eprintf "%a@." R1CS.pp_elem res;
    ) fs;

  prerr_endline "*** R1CS";
  let r1cs = R1CS.of_flatten_list vars fs in
  Format.eprintf "%a@." R1CS.pp r1cs;

  prerr_endline "*** check R1CS";
  R1CS.check r1cs sol;

  prerr_endline "*** QAP";

  let qa, qb, qc = QAP.of_R1CS r1cs in
  prerr_endline "QA";
  let pp_q ppf (s,p) =
    let xpxs =
      List.map (fun x -> x, PQ.apply p x)
        (List.init 4 (fun i -> Q.of_int (i+1)))
    in
    Format.fprintf ppf "%s: %a | %a"
      s
      PQ.pp p
      (Format.pp_print_list ~pp_sep:(pp_list_sep " ") (fun ppf (x,px) ->
           Format.fprintf ppf "p(%a)=%a" Q.pp_print x Q.pp_print px))
      xpxs
  in
  List.iter (Format.eprintf "%a@." pp_q) qa;
  prerr_endline "QB";
  List.iter (Format.eprintf "%a@." pp_q) qb;
  prerr_endline "QC";
  List.iter (Format.eprintf "%a@." pp_q) qc;

  let mul_sol qx =
    (* qx . s *)
    List.fold_left PQ.add PQ.zero
    @@ List.map (fun (s,f) ->
        let x = List.assoc s sol in
        PQ.mul_scalar (Q.of_int x) f) qx
  in

  (* A.s * B.s - C.s *)
  prerr_endline "*** A.s * B.s - C.s";
  let qas = mul_sol qa in
  let qbs = mul_sol qb in
  let qcs = mul_sol qc in
  Format.eprintf "A.s = %a@." PQ.pp qas;
  Format.eprintf "B.s = %a@." PQ.pp qbs;
  Format.eprintf "C.s = %a@." PQ.pp qcs;

  let t = PQ.(add (mul qas qbs) (neg qcs)) in
  Format.eprintf "T = A.s * B.s - C.s = %a@." PQ.pp t;

  (* QAP check *)
  prerr_endline "*** QAP check";

  let q = Q.of_int in
  let z = List.fold_left PQ.mul PQ.one
      [ [q (-1); q 1];
        [q (-2); q 1];
        [q (-3); q 1];
        [q (-4); q 1] ]
  in
  Format.eprintf "Z = %a@." PQ.pp z;
  let div, rem = PQ.div_rem t z in
  Format.eprintf "T/Z = %a@." PQ.pp div;
  Format.eprintf "T mod Z = %a@." PQ.pp rem
