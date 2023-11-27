type ('a, 's) t = 's -> 'a * 's

let (let*) : ('a, 's) t -> ('a -> ('b, 's) t) -> ('b, 's) t =
  fun at f ->
  fun s ->
  let a, s = at s in
  f a s

let (let+) : ('a, 's) t -> ('a -> 'b) -> ('b, 's) t =
  fun at f ->
  fun s ->
  let a, s = at s in
  let b = f a in
  b, s

let return : 'a -> ('a, 's) t = fun a -> fun s -> a, s
