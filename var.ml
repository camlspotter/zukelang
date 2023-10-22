type var = string

type t =var

let compare = String.compare

let pp ppf s = Format.pp_print_string ppf s

module Set = Set.Make(struct
    type nonrec t = t
    let compare = compare
  end)
