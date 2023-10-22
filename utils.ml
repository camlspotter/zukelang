let pp_list_sep fmt ppf () = Format.fprintf ppf fmt

module List = struct
  include List

  let rec drop n xs =
    if n <= 0 then xs else match xs with [] -> [] | _ :: xs -> drop (n - 1) xs

  let take n xs =
    let rec take_ n st xs =
      if n <= 0 then st
      else match xs with [] -> st | x :: xs -> take_ (n - 1) (x :: st) xs
    in
    rev (take_ n [] xs)
end

module Q = struct
  include Q

  let pp = pp_print
end

module type Printable = sig
  type t

  val pp : Format.formatter -> t -> unit
end
