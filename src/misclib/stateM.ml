include Monad.Make2(struct
    type ('a, 's) t = 's -> 'a * 's

    let bind : ('a, 's) t -> ('a -> ('b, 's) t) -> ('b, 's) t =
      fun at f ->
      fun s ->
      let a, s = at s in
      f a s

    let map : ('a -> 'b) ->  ('a, 's) t -> ('b, 's) t =
      fun f at ->
      fun s ->
      let a, s = at s in
      let b = f a in
      b, s

    let return : 'a -> ('a, 's) t = fun a -> fun s -> a, s
  end)
