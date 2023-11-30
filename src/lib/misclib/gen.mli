type rng = Random.State.t

val init_auto : unit -> rng

type 'a t = rng -> 'a

include Monad.T with type 'a t := 'a t

val int : int -> int t

val bool : bool t

val with_rng : (rng -> 'a) -> 'a
