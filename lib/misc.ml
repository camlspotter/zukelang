type 'a printer = Format.formatter -> 'a -> unit

module Format = struct
  include Format

  let list sep f =
    let open Format in
    pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf sep) f

  let seq sep f ppf s =
    let open Format in
    let rec loop o s =
      match o, s () with
      | None, Seq.Nil -> ()
      | None, Cons (a, at) -> loop (Some a) at
      | Some a, Nil -> f ppf a
      | Some a, Cons (a', at) ->
          f ppf a;
          fprintf ppf sep;
          loop (Some a') at
    in
    loop None s

  let f = fprintf

  let ef = eprintf

  let flip = Fun.flip

  let int = pp_print_int

  let string = pp_print_string
end

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

module Option = struct
  include Option

  module Syntax = struct
    let (let*) = bind
    let (let+) x f = map f x
  end

  open Syntax

  let mapM f xs =
    let rec loop acc = function
      | [] -> Some (List.rev acc)
      | x::xs ->
          let* y = f x in
          loop (y::acc) xs
    in
    loop [] xs

  module Monad = struct
    include Syntax
    let mapM = mapM
  end
end

module Q = struct
  include Q

  let pp = pp_print
end

module Gen = struct
  type 'a t = Random.State.t -> 'a
end

module Seq = struct
  include Seq

  let mapi f t =
    let rec aux n t =
      fun () ->
        match t () with
        | Nil -> Nil
        | Cons (x, t) ->
            let x = f n x in
            let t = aux (n+1) t in
            Cons (x, t)
    in
    aux 0 t
end
