module type S = sig
  type +'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val map : ('a -> 'b) -> 'a t -> 'b t

  val return : 'a -> 'a t
end

module type T = sig
  include S

  val mapM : ('a -> 'b t) -> 'a list -> 'b list t

  val fold_leftM : ('acc -> 'a -> 'acc t) -> 'acc -> 'a list -> 'acc t

  module Syntax : sig

    val (let*) : 'a t -> ('a -> 'b t) -> 'b t

    val (let+) : 'a t -> ('a -> 'b) -> 'b t

    val return : 'a -> 'a t

  end
end

module Make(M : S) = struct
  include M

  module Syntax = struct
    let (let*) = M.bind

    let (let+) x f = M.map f x

    let return = M.return
  end

  open Syntax

  let mapM f xs =
    let rec loop acc = function
      | [] -> return (List.rev acc)
      | x::xs ->
          let* y = f x in
          loop (y::acc) xs
    in
    loop [] xs

  let fold_leftM f acc xs =
    let rec g acc = function
      | [] -> return acc
      | x::xs ->
          let* acc = f acc x in
          g acc xs
    in
    g acc xs
end

module type S2 = sig
  type (+'a, 'z) t

  val bind : ('a, 'z) t -> ('a -> ('b, 'z) t) -> ('b, 'z) t

  val map : ('a -> 'b) -> ('a, 'z) t -> ('b, 'z) t

  val return : 'a -> ('a, _) t
end

module type T2 = sig
  include S2

  val mapM : ('a -> ('b, 'z) t) -> 'a list -> ('b list, 'z) t

  val fold_leftM : ('acc -> 'a -> ('acc, 'z) t) -> 'acc -> 'a list -> ('acc, 'z) t

  module Syntax : sig

    val (let*) : ('a, 'z) t -> ('a -> ('b, 'z) t) -> ('b, 'z) t

    val (let+) : ('a, 'z) t -> ('a -> 'b) -> ('b, 'z) t

    val return : 'a -> ('a, 'z) t
  end
end

module Make2(M : S2) = struct
  include M

  module Syntax = struct
    let (let*) = M.bind

    let (let+) x f = M.map f x

    let return = M.return
  end

  open Syntax

  let mapM f xs =
    let rec loop acc = function
      | [] -> return (List.rev acc)
      | x::xs ->
          let* y = f x in
          loop (y::acc) xs
    in
    loop [] xs

  let fold_leftM f acc xs =
    let rec g acc = function
      | [] -> return acc
      | x::xs ->
          let* acc = f acc x in
          g acc xs
    in
    g acc xs
end
