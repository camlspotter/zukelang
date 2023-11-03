open Misc

type var = string

type t = var

let compare = String.compare

let pp ppf s = Format.string ppf s

let of_string x = x

let to_string x = x

module Set = struct
  include Set.Make (struct
    type nonrec t = t

    let compare = compare
  end)

  let pp ppf t = Format.(f ppf "@[%a@]" (list ",@ " pp) (elements t))
end

module Map = struct
  include Map.Make (struct
      type nonrec t = t

      let compare = compare
    end)

  let of_set s f =
    of_seq (Seq.map (fun v -> v, f v) (Set.to_seq s))

  let domain m = Set.of_seq @@ Seq.map fst @@ to_seq m

  let of_list s = of_seq @@ List.to_seq s

  let pp pp_a ppf m =
    Format.(seq ",@ "
              (fun ppf (v,a) -> f ppf "%a = %a" pp v pp_a a)
              ppf
            @@ to_seq m)

  let concat a b = union (fun _ _ _ -> invalid_arg "concat") a b
end

module Infix = struct
  let (#!) l k =
    match Map.find_opt k l with
    | Some res -> res
    | None ->
        Format.ef "Variable %a not found@." pp k;
        assert false
end
