type error = ..

type t = error

val to_string : error -> string

val register_printer : (error -> string option) -> unit

type error +=
  | Exn of exn
  | String of string

type nonrec 'a result = ('a, error) result
(** Result type with the error *)

module Monad : Monad.S with type 'a t = 'a result
