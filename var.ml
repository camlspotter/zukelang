open Utils

type var = string

type t = var

let compare = String.compare

let pp ppf s = Format.string ppf s

let of_string x = x

let to_string x = x

module Set = Set.Make (struct
  type nonrec t = t

  let compare = compare
end)
