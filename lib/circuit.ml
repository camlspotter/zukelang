open Misc

let one = Var.of_string "$ONE"

let out = Var.of_string "$OUT"

module Make(F : Field.COMPARABLE) = struct
  let one = one
  let out = out

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
      inputs_public : Var.Set.t;
      outputs : Var.Set.t;
      mids : Var.Set.t
    }

  type t = circuit

  let pp ppf { gates; inputs_public; outputs; mids } =
    let open Format in
    f ppf "{ @[<v>gates= @[<v>%a@];@ inputs_public= @[%a@];@ outputs= @[%a@];@ mids= @[%a@]@] }"
      Gate.Set.pp gates
      Var.Set.pp inputs_public
      Var.Set.pp outputs
      Var.Set.pp mids

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

  let ios t =
    let vars = vars t.gates in
    Var.Set.diff vars t.mids
end
