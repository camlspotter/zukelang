type t = exn

val to_string : t -> string

val catch : (unit -> 'a) -> 'a Error.result

val catch_as_string : (unit -> 'a) -> ('a, string) result
