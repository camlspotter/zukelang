open Utils

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
end
