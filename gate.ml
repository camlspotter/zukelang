open Utils
open Expr

(* x = (2y + 3one) * (3z + 4w + 6one) *)
type gate =
  Var.t * (Var.t * int) list * (Var.t * int) list

let one = Var.of_string "~one"

let out = Var.of_string "~out"

let pp_gate ppf (v, l, r : gate) =
  let open Format in
  let f = fprintf in
  let pp_arg ppf xs =
    Format.list " + "
      (fun ppf (v, n) ->
         if v = one then
           int ppf n
         else
           f ppf "%d%a" n Var.pp v)
      ppf
      xs
  in
  f ppf "%a = (%a) * (%a)"
    Var.pp v
    pp_arg l
    pp_arg r

type t =
  { gates : gate list;
    mids : Var.Set.t
  }

let pp_gates = Format.list "@," pp_gate

let pp ppf t =
  let open Format in
  f ppf "{ @[<v>gates= @[%a@];@ mids= @[%a@]@] }"
    (list "@," pp_gate) t.gates
    (list ", " Var.pp) (Var.Set.elements t.mids)

let vars gates =
  List.fold_left (fun acc (g, l, r) ->
      let vs = g :: List.map fst l @ List.map fst r in
      Var.Set.add_seq (List.to_seq vs) acc) Var.Set.empty gates

let eval_gate_binding (env : (Var.t * int) list) (vns1, vns2) =
  let open Option.Monad in
  let* a1 =
    Option.mapM (fun (v,n) ->
        let+ a = List.assoc_opt v env in
        a * n) vns1
  in
  let+ a2 =
    Option.mapM (fun (v,n) ->
        let+ a = List.assoc_opt v env in
        a * n) vns2
  in
  List.fold_left (+) 0 a1
  * List.fold_left (+) 0 a2

let eval env gates =
  let vars = vars gates in
  let unks =
    List.fold_left (fun acc (v, _) -> Var.Set.remove v acc) vars env
  in
  let rec loop sol unks rev_fs fs =
    if Var.Set.is_empty unks then Ok sol
    else
      match fs with
      | [] -> Error sol
      | ((v, vns1, vns2) as f) :: fs -> (
          match eval_gate_binding sol (vns1, vns2) with
          | Some i ->
              loop
                ((v, i) :: sol)
                (Var.Set.remove v unks)
                []
                (List.rev_append rev_fs fs)
          | None -> loop sol unks (f :: rev_fs) fs)
  in
  loop env unks [] gates

module Expr' = struct
  type expr' = expr'' list

  and expr'' =
    | Term of Var.t option * int
    | Mul of expr' * expr'

  let rec pp_expr' ppf e's =
    let open Format in
    f ppf "@[%a@]"
      (pp_print_list ~pp_sep:(fun ppf () -> f ppf "@ + ") pp_expr'') e's

  and pp_expr'' ppf =
    let open Format in
    function
    | Term (None, n) -> int ppf n
    | Term (Some v, n) -> f ppf "%d%a" n Var.pp v
    | Mul (e1, e2) -> f ppf "@[(%a) * (%a)@]" pp_expr' e1 pp_expr' e2

end

let rec expr' (e : Expr.t) : Expr'.expr' =
  match e with
  | Term (Int n) -> [Term (None, n)]
  | Term (Var v) -> [Term (Some v, 1)]
  | BinApp (Mul, e1, e2) ->
      let e1 = expr' e1 in
      let e2 = expr' e2 in
      [Mul (e1, e2)]
  | BinApp (Add, e1, e2) ->
      let es = expr' e1 @ expr' e2 in
      let terms, muls =
        List.partition_map (function
            | Expr'.Term (vo,n) -> Left (vo,n)
            | Mul _ as e -> Right e) es
      in
      let terms =
        let module Map = Map.Make(struct
            type t = Var.t option
            let compare = compare
          end)
        in
        Map.bindings @@
        List.fold_left (fun acc (vo,n) ->
            Map.update vo (function
                | None -> Some n
                | Some n' -> Some (n+n')) acc)
          Map.empty terms
      in
      List.map (fun (vo,n) -> Expr'.Term (vo,n)) terms @ muls

let mk_mk_var () =
  let cntr = ref 0 in
  fun () ->
    incr cntr;
    Var.of_string (Printf.sprintf "_tmp%d" !cntr)

let rec build (mk_var : unit -> Var.t) (e : Expr'.expr'') : (Var.t * int) * gate list =
  match e with
  | Term (None, n) -> (one, n), []
  | Term (Some v, n) -> (v, n), []
  | Mul (e1, e2) ->
      let sum1, gs1 =
        List.fold_left (fun (sum, gs) e ->
            let (v,w), gs' = build mk_var e in
            ((v,w)::sum, gs @ gs')) ([], []) e1
      in
      let sum2, gs2 =
        List.fold_left (fun (sum, gs) e ->
            let (v,w), gs' = build mk_var e in
            ((v,w)::sum, gs @ gs')) ([], []) e2
      in
      let v = mk_var () in
      (v, 1), (v, sum1, sum2) :: gs1 @ gs2

and build' mk_var (e : Expr'.expr') =
  let vns, gss = List.split @@ List.map (build mk_var) e in
  let gs = List.concat gss in
  (out, vns, [(one, 1)]) :: gs

let of_expr (e : Expr.t) =
  let e' = expr' e in
  let mk_var = mk_mk_var () in
  build' mk_var e'

let is_mid v = (Var.to_string v).[0] = '_'

let is_io v = (Var.to_string v).[0] <> '_'

let mids =
  List.filter_map (fun (v, _, _) ->
      if is_mid v then Some v else None)

let ios gates =
  List.filter_map (fun v ->
      if is_io v then Some v else None)
  @@ Var.Set.elements @@ vars gates

let test () =
  let open Expr in
  let open Expr.Infix in
  let x = var "x" in
  let e = x * x * x + x + int 3 in
  let open Format in
  ef "----------------@.";
  ef "Expr: %a@." Expr.pp e;
  let e' = expr' e in
  ef "Expr': %a@." Expr'.pp_expr' e';
  let mk_var = mk_mk_var () in
  let gs = build' mk_var e' in
  ef "Gates: @[<v>%a@]@." pp_gates gs
