open Misclib

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

  let ios t =
    let vars = vars t.gates in
    Var.Set.diff vars t.mids
end
