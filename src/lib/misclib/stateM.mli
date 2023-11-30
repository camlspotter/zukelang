(** State monad *)

include Monad.T2 with type ('a, 's) t = 's -> 'a * 's
