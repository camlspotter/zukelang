(* https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649 *)

open Utils

module PQ = Polynomial.Make (Q)

type q = Var.var * PQ.polynomial

type t = q list Abc.t

let of_R1CS_rows rows : q list =
  let trans = R1CS.transpose rows in
    (*
    List.iter (fun (n, xs) ->
        Format.(eprintf "@[%s: %a@]@."
                  n
                  (pp_print_list ~pp_sep:(pp_list_sep ";@ ") pp_print_int) xs))
      trans;
    *)
  let ps =
    List.map
      (fun (n, xs) ->
         let xs = List.rev xs in
         let xys = List.mapi (fun i x -> (Q.of_int (i + 1), Q.of_int x)) xs in
         (n, PQ.interporate xys))
      trans
  in
    (*
    List.iter (fun (n,p) -> Format.eprintf "%s: %a@." n PQ.pp p) ps;
    *)
  ps

let of_R1CS Abc.{a; b; c} : t =
  { a= of_R1CS_rows a; b= of_R1CS_rows b; c= of_R1CS_rows c }

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
