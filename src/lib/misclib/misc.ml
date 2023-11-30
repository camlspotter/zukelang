type 'a comparator = 'a -> 'a -> int

let with_time f =
  let t1 = Unix.gettimeofday () in
  let res = f () in
  let t2 = Unix.gettimeofday () in
  res, t2 -. t1

let log2 =
  let l2 = log 2.0 in
  fun f -> log f /. l2

let failwithf fmt = Format.kasprintf failwith fmt
let invalid_argf fmt = Format.kasprintf invalid_arg fmt

module Converter = struct
  module type S = sig
    type src
    type dst
    val encode : src -> dst
    val decode : dst -> src Error.result
  end
end

module Z = struct
  include Z
  let pp = pp_print

  open JSON.Conv

  let yojson_of_t z = yojson_of_string @@ Z.to_string z

  let t_of_yojson j = Z.of_string @@ string_of_yojson j
end

module Q = struct
  include Q

  type nonrec t = Q.t = { num : Z.t; den : Z.t } [@@deriving yojson]

  let pp = pp_print

  let is_zero x = Q.(x = zero)
end
