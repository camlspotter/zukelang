include Stdlib.Option

module Syntax = struct
  let (let*) = bind
  let (let+) x f = map f x
end

open Syntax

let mapM f xs =
  let rec loop acc = function
    | [] -> Some (List.rev acc)
    | x::xs ->
        let* y = f x in
        loop (y::acc) xs
  in
  loop [] xs

module Monad = struct
  include Syntax
  let mapM = mapM
end
