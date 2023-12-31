type rng = Random.State.t

let init_auto = Random.State.make_self_init

include Monad.Make(struct
    type 'a t = rng -> 'a

    let return a _rng = a

    let bind : 'a t -> ('a -> 'b t) -> 'b t = fun at f ->
      fun rng ->
        let a = at rng in
        f a rng

    let map : ('a -> 'b) -> 'a t -> 'b t = fun f at ->
      fun rng ->
        let a = at rng in
        f a
  end)

let int sz rng = Random.State.int rng sz

let uint32 =
  if Sys.word_size < 64 then assert false;
  fun rng ->
    let i1 = Random.State.bits rng in
    let i2 = Random.State.bits rng in
    i1 + (i2 land 0b11) lsl 30

let bool rng = int 2 rng <> 0

let with_rng f =
  let rng = init_auto () in
  f rng
