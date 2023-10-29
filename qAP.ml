(* https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649 *)

open Utils

type 'f q = Var.t * 'f Polynomial.t

type 'f t = 'f q list Abc.t

module Make(F : Field.S) = struct
  module Poly = Polynomial.Make(F)

  type nonrec q = F.t q

  type t = q list Abc.t

  let of_R1CS_rows rows : q list =
    let trans = R1CS.transpose rows in
    List.map
      (fun (n, xs) ->
         let xs = List.rev xs in
         let xys = List.mapi (fun i x -> (F.of_int (i + 1), F.of_int x)) xs in
         (n, Poly.interpolate xys))
      trans

  let of_R1CS = Abc.map of_R1CS_rows

  let pp_q ppf (s, p) =
    let open Format in
    let xpxs =
      List.map
        (fun x -> (x, Poly.apply p x))
        (List.init 4 (fun i -> F.of_int (i + 1)))
    in
    f ppf
      "%a: %a | %a"
      Var.pp s
      Poly.pp p
      (list " " (fun ppf (x, px) ->
           f ppf "p(%a)=%a" F.pp x F.pp px)) xpxs

  let pp =
    let open Format in
    let pp_qs ppf qs =
      f ppf "@[<v>";
      List.iter (Format.fprintf ppf "%a;@," pp_q) qs ;
      f ppf "@]"
    in
    Abc.pp pp_qs

  let mul_sol_q_list (qx : q list) (sol : (Var.var * int) list) : Poly.t =
    (* qx . sol *)
    Poly.sum
    @@ List.map
      (fun (s, f) ->
         let x = List.assoc s sol in
         Poly.mul_scalar (F.of_int x) f)
      qx

  let mul_sol t sol = Abc.map (fun x -> mul_sol_q_list x sol) t
end

let conv f = Abc.map (List.map (fun (v, p) -> v, Polynomial.conv f p))
