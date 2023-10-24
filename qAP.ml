(* https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649 *)

open Utils

module PQ = Polynomial.Make (Q)

type q = Var.var * PQ.polynomial

type t = q list Abc.t

let of_R1CS_rows rows : q list =
  let trans = R1CS.transpose rows in
  List.map
    (fun (n, xs) ->
       let xs = List.rev xs in
       let xys = List.mapi (fun i x -> (Q.of_int (i + 1), Q.of_int x)) xs in
       (n, PQ.interporate xys))
    trans

let of_R1CS = Abc.map of_R1CS_rows

let pp_q ppf (s, p) =
  let open Format in
  let xpxs =
    List.map
      (fun x -> (x, PQ.apply p x))
      (List.init 4 (fun i -> Q.of_int (i + 1)))
  in
  fprintf
    ppf
    "%a: %a | %a"
    Var.pp
    s
    PQ.pp
    p
    (pp_print_list ~pp_sep:(pp_list_sep " ") (fun ppf (x, px) ->
         fprintf ppf "p(%a)=%a" Q.pp_print x Q.pp_print px))
    xpxs

let pp =
  let pp_qs ppf qs =
    Format.fprintf ppf "@[<v>";
    List.iter (Format.fprintf ppf "%a;@," pp_q) qs ;
    Format.fprintf ppf "@]"
  in
  Abc.pp pp_qs

let mul_sol_QAP_q_list (qx : q list) (sol : (Var.var * int) list) : PQ.t =
    (* qx . sol *)
    List.fold_left PQ.add PQ.zero
    @@ List.map
         (fun (s, f) ->
           let x = List.assoc s sol in
           PQ.mul_scalar (Q.of_int x) f)
         qx

let mul_sol t sol =
  Abc.map (fun x -> mul_sol_QAP_q_list x sol) t
