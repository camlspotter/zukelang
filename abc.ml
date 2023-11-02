open Utils

type 'a t = {a : 'a; b : 'a; c : 'a}

let pp pp_t ppf {a; b; c} =
  let open Format in
  f ppf "{ @[<v>" ;
  f ppf "a: @[%a@];@ " pp_t a ;
  f ppf "b: @[%a@];@ " pp_t b ;
  f ppf "c: @[%a@];@ " pp_t c ;
  f ppf "@] }"

let map f {a; b; c} = {a = f a; b = f b; c = f c}

let split abcs =
  let a = List.map (fun t -> t.a) abcs in
  let b = List.map (fun t -> t.b) abcs in
  let c = List.map (fun t -> t.c) abcs in
  {a; b; c}