open Utils

open Lang

let one = Var.of_string "~one"

let out = Var.of_string "~out"

module Make(F : Field.S) = struct

  let one = one
  let out = out

  module Lang = Lang.Make(F)
  open Lang

  module Gate = struct
    (* (2y + 3one) * (3z + 4w + 6one) *)
    type gate = F.t Var.Map.t * F.t Var.Map.t

    type t = gate

    let pp ppf (l, r : gate) =
      let open Format in
      let f = fprintf in
      let pp_arg ppf xs =
        Format.seq " + "
          (fun ppf (v, n) ->
             if v = one then
               F.pp ppf n
             else
               f ppf "%a%a" F.pp n Var.pp v)
          ppf
          @@ Var.Map.to_seq xs
      in
      f ppf "(%a) * (%a)"
        pp_arg l
        pp_arg r
  end

  type gates = Gate.t Var.Map.t

  let equal_gates gs1 gs2 =
    Var.Map.equal (fun (l1, r1) (l2, r2) ->
        Var.Map.equal F.(=) l1 l2
        && Var.Map.equal F.(=) r1 r2) gs1 gs2

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
        let vs = Var.Set.(add g (union (Var.Map.domain l) (Var.Map.domain r))) in
        Var.Set.union vs acc) gates Var.Set.empty

  let eval_gate_binding env (vns1, vns2) =
    let open Option.Monad in
    let open F in
    let* a1 =
      Option.mapM (fun (v,n) ->
          let+ a = Var.Map.find_opt v env in
          a * n) @@ Var.Map.bindings vns1
    in
    let+ a2 =
      Option.mapM (fun (v,n) ->
          let+ a = Var.Map.find_opt v env in
          a * n) @@ Var.Map.bindings vns2
    in
    List.fold_left (+) zero a1
    * List.fold_left (+) zero a2

  let eval env gates =
    let vars = vars gates in
    let unks =
      Var.Map.fold (fun v _ acc -> Var.Set.remove v acc) env vars
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
                  (Var.Map.add v i sol)
                  (Var.Set.remove v unks)
                  []
                  (List.rev_append rev_fs fs)
            | None -> loop sol unks (f :: rev_fs) fs)
    in
    loop env unks [] (Var.Map.bindings gates) (* may be slow *)

  module Expr' = struct
    type expr' = expr'' list

    and expr'' =
      | Term of Var.t option * F.t
      | Mul of expr' * expr'

    let rec pp_expr' ppf e's =
      let open Format in
      f ppf "@[%a@]"
        (pp_print_list ~pp_sep:(fun ppf () -> f ppf "@ + ") pp_expr'') e's

    and pp_expr'' ppf =
      let open Format in
      function
      | Term (None, n) -> F.pp ppf n
      | Term (Some v, n) -> f ppf "%a%a" F.pp n Var.pp v
      | Mul (e1, e2) -> f ppf "@[(%a) * (%a)@]" pp_expr' e1 pp_expr' e2
  end

  let rec expr' (e : Expr.t) : Expr'.expr' =
    match e with
    | Term (Num n) -> [Term (None, n)]
    | Term (Var v) -> [Term (Some v, F.one)]
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
                  | Some n' -> Some F.(n+n')) acc)
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
    let rec aux (e : Expr'.expr'') =
      let open Var.Map in
      match e with
      | Term (None, n) -> (one, n), empty
      | Term (Some v, n) -> (v, n), empty
      | Mul (e1, e2) ->
          let sum1, gs1 =
            List.fold_left (fun (sum, gs) e ->
                let (v,w), gs' = aux e in
                (add v w sum, concat gs gs')) (empty, empty) e1
          in
          let sum2, gs2 =
            List.fold_left (fun (sum, gs) e ->
                let (v,w), gs' = aux e in
                (add v w sum, concat gs gs')) (empty, empty) e2
          in
          let v = mk_var () in
          (v, F.one), add v (sum1, sum2) @@ concat gs1 gs2
    in
    let vns, gss = List.split @@ List.map aux e in
    let gs = List.fold_left Var.Map.concat Var.Map.empty gss in
    { gates = Var.Map.add out (Var.Map.of_list vns, Var.Map.singleton one F.one) gs;
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
      let open Expr.Infix in
      x * x * x + x + !!! 3
    in
    let open Format in
    ef "----------------@.";
    ef "Expr: %a@." Expr.pp e;
    let e' = expr'  e in
    ef "Expr': %a@." Expr'.pp_expr' e';
    let t = build e' in
    ef "Gates: @[<v>%a@]@." pp t
end
