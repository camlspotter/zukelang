open Utils
open Expr

let one = Var.of_string "~one"

let out = Var.of_string "~out"

module Gate = struct
  (* (2y + 3one) * (3z + 4w + 6one) *)
  type gate = (Var.t * int) list * (Var.t * int) list

  type t = gate

  let pp ppf (l, r : gate) =
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
    f ppf "(%a) * (%a)"
      pp_arg l
      pp_arg r
end

type gates = Gate.t Var.Map.t

let pp_gates ppf (gates : gates) =
  let open Format in
  list ",@ "
    (fun ppf (v,g) ->
       f ppf "%a = %a" Var.pp v Gate.pp g) ppf
  @@ Var.Map.bindings gates

type circuit =
  { gates : Gate.t Var.Map.t;
    mids : Var.Set.t
  }

type t = circuit

let pp ppf t =
  let open Format in
  f ppf "{ @[<v>gates= @[<v>%a@];@ mids= @[%a@]@] }"
    pp_gates t.gates
    (list ", " Var.pp) (Var.Set.elements t.mids)

let vars gates =
  Var.Map.fold (fun g (l,r) acc ->
      let vs = g :: List.map fst l @ List.map fst r in
      Var.Set.add_seq (List.to_seq vs) acc) gates Var.Set.empty

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
      | ((v, (vns1, vns2)) as f) :: fs -> (
          match eval_gate_binding sol (vns1, vns2) with
          | Some i ->
              loop
                ((v, i) :: sol)
                (Var.Set.remove v unks)
                []
                (List.rev_append rev_fs fs)
          | None -> loop sol unks (f :: rev_fs) fs)
  in
  loop env unks [] (Var.Map.bindings gates) (* may be slow *)

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

let build (e : Expr'.expr') =
  let mids = ref Var.Set.empty in
  let mk_var =
    let cntr = ref 0 in
    fun () ->
      incr cntr;
      let v = Var.of_string (Printf.sprintf "_tmp%d" !cntr) in
      mids := Var.Set.add v !mids;
      v
  in
  let rec aux (e : Expr'.expr'') : (Var.t * int) * (Var.t * Gate.t) list =
    match e with
    | Term (None, n) -> (one, n), []
    | Term (Some v, n) -> (v, n), []
    | Mul (e1, e2) ->
        let sum1, gs1 =
          List.fold_left (fun (sum, gs) e ->
              let (v,w), gs' = aux e in
              ((v,w)::sum, gs @ gs')) ([], []) e1
        in
        let sum2, gs2 =
          List.fold_left (fun (sum, gs) e ->
              let (v,w), gs' = aux e in
              ((v,w)::sum, gs @ gs')) ([], []) e2
        in
        let v = mk_var () in
        (v, 1), (v, (sum1, sum2)) :: gs1 @ gs2
  in
  let vns, gss = List.split @@ List.map aux  e in
  let gs = List.concat gss in
  { gates = Var.Map.of_seq @@ List.to_seq ((out, (vns, [(one, 1)])) :: gs);
    mids= !mids }

let of_expr (e : Expr.t) =
  let e' = expr' e in
  build e'

let ios t =
  let vars = vars t.gates in
  Var.Set.diff vars t.mids

let test () =
  let x = Expr.var "x" in
  let e =
    let open Expr in
    let open Expr.Infix in
    x * x * x + x + int 3
  in
  let open Format in
  ef "----------------@.";
  ef "Expr: %a@." Expr.pp e;
  let e' = expr' e in
  ef "Expr': %a@." Expr'.pp_expr' e';
  let t = build e' in
  ef "Gates: @[<v>%a@]@." pp t
