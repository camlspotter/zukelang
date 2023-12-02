type rng = Random.State.t

val init_auto : unit -> rng

type 'a t = rng -> 'a

include Monad.T with type 'a t := 'a t

val int : int -> int t
(** Upto 2{^30}-1 *)

val uint32 : int t
(** [0..2{^32-1}] *)

val bool : bool t

val with_rng : (rng -> 'a) -> 'a
