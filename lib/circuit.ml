open Misc

open Lang

let one = Var.of_string "$ONE"

let out = Var.of_string "$OUT"

module Make(F : Field.COMPARABLE) = struct
  let one = one
  let out = out

  module Lang = Lang.Make(F)
  open Lang

  module Affine = struct
    type affine = F.t Var.Map.t

    type t = affine

    let pp ppf m =
      let open Format in
      if Var.Map.is_empty m then
        Format.f ppf "0"
      else
        Format.seq " + "
          (fun ppf (v, n) ->
             if v = one then
               F.pp ppf n
             else if F.(n = one) then
               Var.pp ppf v
             else
               f ppf "%a * %a" F.pp n Var.pp v)
          ppf
        @@ Var.Map.to_seq m

    let compare = Var.Map.compare F.compare

    let singleton = Var.Map.singleton
    let of_var v = singleton v (F.of_int 1)
    let add = Var.Map.union (fun _v f1 f2 -> Some F.(f1 + f2))
    let mul_scalar t f = Var.Map.map F.(( * ) f) t
    let neg t = mul_scalar t (F.of_int (-1))
    let of_F f =
      if F.(f = zero) then Var.Map.empty
      else singleton one f
    let of_int i = of_F (F.of_int i)
    let zero = of_int 0
    let is_zero = Var.Map.is_empty
    let sub a b =
      if is_zero b then a
      else add a (mul_scalar b (F.of_int (-1)))
    let is_const a =
      let a' = Var.Map.remove one a in
      if Var.Map.is_empty a' then
        match Var.Map.find_opt one a with
        | None -> Some F.zero
        | Some f -> Some f
      else None
    let vars = Var.Map.domain

    let eval env a =
      Var.Map.fold (fun v ck acc ->
          F.(Var.Map.find v env * ck + acc)) a F.zero

    module Infix = struct
      let (!) = of_int
      let (+) = add
      let (-) = sub
      let ( *$ ) = mul_scalar
      let (~-) = neg
    end
  end

  module Gate = struct
    (* z + 3 = (2y + 3one) * (3z + 4w + 6one) *)
    type gate = { lhs : Affine.t; l : Affine.t; r : Affine.t }

    type t = gate

    let pp ppf { lhs; l; r } =
      Format.f ppf "@[<2>%a@ = @[@[(%a)@]@ * @[(%a)@]@]@]"
        Affine.pp lhs
        Affine.pp l
        Affine.pp r

    let compare a b =
      match Affine.compare a.lhs b.lhs with
      | 0 ->
          (match Affine.compare a.l b.l with
           | 0 -> Affine.compare a.r b.r
           | n -> n)
      | n -> n

    let vars { lhs; l; r } =
      Var.Set.(union (Affine.vars lhs) @@ union (Affine.vars l) (Affine.vars r))

    module Set = struct
      include Set.Make(struct
          type t = gate
          let compare = compare
        end)

      let pp ppf s = Format.(seq ",@ " pp ppf @@ to_seq s)

      let vars gs = fold (fun gate acc -> Var.Set.union (vars gate) acc) gs Var.Set.empty
    end
  end

  type circuit =
    { gates : Gate.Set.t;
      inputs : Var.Set.t;
      outputs : Var.Set.t;
      mids : Var.Set.t
    }

  type t = circuit

  let pp ppf t =
    let open Format in
    f ppf "{ @[<v>gates= @[<v>%a@];@ mids= @[%a@]@] }"
      Gate.Set.pp t.gates
      (list ", " Var.pp) (Var.Set.elements t.mids)

  let vars gates =
    Gate.Set.fold (fun {lhs; l; r} acc ->
        let lhs = Var.Map.domain lhs in
        let l = Var.Map.domain l in
        let r = Var.Map.domain r in
        Var.Set.(union (union lhs (union l r)) acc)) gates Var.Set.empty

  (* OBSOLETE *)
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

  (* OBSOLETE *)
  let eval env gates =
    let vars = vars gates in
    let unks = Var.Set.diff vars (Var.Map.domain env) in
    let gates = Gate.Set.elements gates in
    let rec loop sol unks rev_gs gs =
      if Var.Set.is_empty unks then Ok sol
      else
        match gs with
        | [] -> Error sol
        | (Gate.{lhs; l= vns1; r= vns2} as g) :: gs ->
            (* lhs must be a singleton of (v, 1) *)
            match Var.Map.bindings lhs with
            | [(v, f)] when F.(f = one) ->
                (match eval_gate_binding sol (vns1, vns2) with
                 | Some i ->
                     loop
                       (Var.Map.add v i sol)
                       (Var.Set.remove v unks)
                       [] (List.rev_append rev_gs gs)
                 | None -> loop sol unks (g::rev_gs) gs)
            | _ -> invalid_arg "Circuit.eval"
    in
    loop env unks [] gates

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

    let vars e' =
      let open Var.Set in
      let rec f'' = function
        | Term (Some v, _) -> singleton v
        | Term (None, _) -> empty
        | Mul (e'1, e'2) -> union (f' e'1) (f' e'2)
      and f' e''s =
        List.fold_left (fun acc e'' -> union acc (f'' e'')) empty e''s
      in
      f' e'

    let rec expr' (e : Expr.t) : expr' =
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
                | Term (vo,n) -> Left (vo,n)
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
          List.map (fun (vo,n) -> Term (vo,n)) terms @ muls
  end

  let build (e : Expr'.expr') =
    let inputs = Var.Set.add one @@ Expr'.vars e in
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
      match e with
      | Term (None, n) -> (one, n), Gate.Set.empty
      | Term (Some v, n) -> (v, n), Gate.Set.empty
      | Mul (e1, e2) ->
          let sum1, gs1 =
            List.fold_left (fun (sum, gs) e ->
                let (v,w), gs' = aux e in
                (Var.Map.add v w sum, Gate.Set.union gs gs')) (Var.Map.empty, Gate.Set.empty) e1
          in
          let sum2, gs2 =
            List.fold_left (fun (sum, gs) e ->
                let (v,w), gs' = aux e in
                (Var.Map.add v w sum, Gate.Set.union gs gs')) (Var.Map.empty, Gate.Set.empty) e2
          in
          let v = mk_var () in
          ( (v, F.one),
            Gate.Set.add { lhs= Var.Map.singleton v F.one ; l= sum1; r= sum2 }
            @@ Gate.Set.union gs1 gs2 )
    in
    let vns, gss = List.split @@ List.map aux e in
    let g : Gate.t =
      { lhs= Var.Map.singleton out F.one; l= Var.Map.of_list vns; r= Var.Map.singleton one F.one }
    in
    let gates = List.fold_left Gate.Set.union (Gate.Set.singleton g) gss in
    { gates; inputs; outputs = Var.Set.singleton out; mids= !mids }

  let of_expr (e : Expr.t) =
    let e' = Expr'.expr' e in
    build e'

  let ios t =
    let vars = vars t.gates in
    Var.Set.diff vars t.mids

  let test () =
    let x = Expr.var "x" in
    let e =
      let open Expr.Infix in
      x * x * x + x + !3
    in
    let open Format in
    ef "----------------@.";
    ef "Expr: %a@." Expr.pp e;
    let e' = Expr'.expr'  e in
    ef "Expr': %a@." Expr'.pp_expr' e';
    let t = build e' in
    ef "Gates: @[<v>%a@]@." pp t
end
