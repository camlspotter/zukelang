(* https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649 *)

open Utils
open Expr
module PQ = Polynomial.Make (Q)

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

  let of_R1CS {R1CS.aa; bb; cc} =
    (of_R1CS_rows aa, of_R1CS_rows bb, of_R1CS_rows cc)
end

let test () =
  let rhs =
    let open Expr in
    add (add (mul (mul (var "x") (var "x")) (var "x")) (var "x")) (int 5)
  in
  assert (Expr.eval [(Var.of_string "x", 3)] rhs = 35) ;
  let lhs = Var.of_string "~out" in
  Format.eprintf "%a = %a@." Var.pp lhs Expr.pp rhs ;

  prerr_endline "*** flatten" ;
  let fs = Flatten.flatten (lhs, rhs) in
  List.iter (fun eq -> Format.eprintf "%a@." Flatten.pp eq) fs ;

  prerr_endline "*** solution vector" ;
  let sol = Flatten.eval [(Var.of_string "x", 3)] fs in
  List.iter (fun (v, n) -> Format.eprintf "%a : %d@." Var.pp v n) sol ;
  let sol = (Var.of_string "~one", 1) :: sol in

  prerr_endline "*** R1CS elems" ;
  let vars = List.of_seq @@ Var.Set.to_seq @@ Flatten.vars fs in
  List.iter
    (fun f ->
      let res = R1CS.of_flatten vars f in
      Format.eprintf "%a@." Flatten.pp f ;
      Format.eprintf "%a@." R1CS.pp_elem res)
    fs ;

  prerr_endline "*** R1CS" ;
  let r1cs = R1CS.of_flatten_list vars fs in
  Format.eprintf "%a@." R1CS.pp r1cs ;

  prerr_endline "*** check R1CS" ;
  R1CS.check r1cs sol ;

  prerr_endline "*** QAP" ;

  let qa, qb, qc = QAP.of_R1CS r1cs in
  prerr_endline "QA" ;
  let pp_q ppf (s, p) =
    let xpxs =
      List.map
        (fun x -> (x, PQ.apply p x))
        (List.init 4 (fun i -> Q.of_int (i + 1)))
    in
    Format.fprintf
      ppf
      "%a: %a | %a"
      Var.pp
      s
      PQ.pp
      p
      (Format.pp_print_list ~pp_sep:(pp_list_sep " ") (fun ppf (x, px) ->
           Format.fprintf ppf "p(%a)=%a" Q.pp_print x Q.pp_print px))
      xpxs
  in
  List.iter (Format.eprintf "%a@." pp_q) qa ;
  prerr_endline "QB" ;
  List.iter (Format.eprintf "%a@." pp_q) qb ;
  prerr_endline "QC" ;
  List.iter (Format.eprintf "%a@." pp_q) qc ;

  let mul_sol qx =
    (* qx . s *)
    List.fold_left PQ.add PQ.zero
    @@ List.map
         (fun (s, f) ->
           let x = List.assoc s sol in
           PQ.mul_scalar (Q.of_int x) f)
         qx
  in

  (* A.s * B.s - C.s *)
  prerr_endline "*** A.s * B.s - C.s" ;
  let qas = mul_sol qa in
  let qbs = mul_sol qb in
  let qcs = mul_sol qc in
  Format.eprintf "A.s = %a@." PQ.pp qas ;
  Format.eprintf "B.s = %a@." PQ.pp qbs ;
  Format.eprintf "C.s = %a@." PQ.pp qcs ;

  let t = PQ.(add (mul qas qbs) (neg qcs)) in
  Format.eprintf "T = A.s * B.s - C.s = %a@." PQ.pp t ;

  (* QAP check *)
  prerr_endline "*** QAP check" ;

  let q = Q.of_int in
  let z =
    List.fold_left
      PQ.mul
      PQ.one
      [[q (-1); q 1]; [q (-2); q 1]; [q (-3); q 1]; [q (-4); q 1]]
  in
  Format.eprintf "Z = %a@." PQ.pp z ;
  let div, rem = PQ.div_rem t z in
  Format.eprintf "H = T/Z = %a@." PQ.pp div ;
  Format.eprintf "T mod Z = %a@." PQ.pp rem
