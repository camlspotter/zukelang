include Stdlib.Result

module Syntax = struct
  let (let*) x f =
    match x with
    | Error e -> Error e
    | Ok a -> f a

  let (let+) x f = map f x

  let return x = Ok x
end
