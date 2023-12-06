type t = exn

type printer = t -> (Format.t -> unit) option

val register_printer : printer -> unit

val pp : t Format.printer

val to_string : t -> string

type exn += String of string

type 'a result = ('a, t) Result.t

module Monad : Monad.T with type 'a t = 'a result

val catch : (unit -> 'a) -> 'a result

val get_ok : 'a result -> 'a
