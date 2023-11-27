(** State monad *)

type ('a, 's) t = 's -> 'a * 's

val (let*) : ('a, 's) t -> ('a -> ('b, 's) t) -> ('b, 's) t

val (let+) : ('a, 's) t -> ('a -> 'b) -> ('b, 's) t

val return : 'a -> ('a, 's) t
