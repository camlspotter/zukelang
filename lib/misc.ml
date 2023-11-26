type 'a printer = Format.formatter -> 'a -> unit
type 'a comparator = 'a -> 'a -> int

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

module Gen = struct
  type 'a t = Random.State.t -> 'a

  let int sz rng = Random.State.int rng sz

  let return a _rng = a
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

let with_time f =
  let t1 = Unix.gettimeofday () in
  let res = f () in
  let t2 = Unix.gettimeofday () in
  res, t2 -. t1

let log2 =
  let l2 = log 2.0 in
  fun f -> log f /. l2

module Result = struct
  include Result
  module Syntax = struct
    let (let*) x f =
      match x with
      | Error e -> Error e
      | Ok a -> f a

    let (let+) x f = map f x

    let return x = Ok x
  end
end

module Converter = struct
  module type S = sig
    type src
    type dst
    val encode : src -> dst
    val decode : dst -> src Error.result
  end
end

module JSON = struct
  type json = Yojson.Safe.t
  type t = json

  type 'a encoder = 'a -> t
  type 'a decoder = t -> ('a, string) result

  module Conv = struct
    open Ppx_yojson_conv_lib
    include Yojson_conv

    module type S = Yojsonable.S
    module type S1 = Yojsonable.S1
    module type S2 = Yojsonable.S2
    module type S3 = Yojsonable.S3
  end
end

module Z = struct
  include Z
  let pp = pp_print

  open Ppx_yojson_conv_lib.Yojson_conv

  let yojson_of_t z = yojson_of_string @@ Z.to_string z

  let t_of_yojson j = Z.of_string @@ string_of_yojson j
end

module Q = struct
  include Q

  type nonrec t = Q.t = { num : Z.t; den : Z.t } [@@deriving yojson]

  let pp = pp_print

  let is_zero x = Q.(x = zero)
end

let failwithf fmt = Format.kasprintf failwith fmt
