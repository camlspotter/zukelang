type rng = Random.State.t

type 'a t = rng -> 'a

let init_auto = Random.State.make_self_init

let int sz rng = Random.State.int rng sz

let return a _rng = a

let (let*) : 'a t -> ('a -> 'b t) -> 'b t = fun at f ->
  fun rng ->
    let a = at rng in
    f a rng

let (let+) : 'a t -> ('a -> 'b) -> 'b t = fun at f ->
  fun rng ->
    let a = at rng in
    f a
