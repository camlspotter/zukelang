module type S = sig
  type +'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val map : ('a -> 'b) -> 'a t -> 'b t

  val return : 'a -> 'a t
end

module type T = sig
  include S

  val mapM : ('a -> 'b t) -> 'a list -> 'b list t

  module Syntax : sig

    val (let*) : 'a t -> ('a -> 'b t) -> 'b t

    val (let+) : 'a t -> ('a -> 'b) -> 'b t

    val return : 'a -> 'a t

  end
end

module Make(M : S) : T with type 'a t = 'a M.t

module type S2 = sig
  type (+'a, 'z) t

  val bind : ('a, 'z) t -> ('a -> ('b, 'z) t) -> ('b, 'z) t

  val map : ('a -> 'b) -> ('a, 'z) t -> ('b, 'z) t

  val return : 'a -> ('a, _) t
end

module type T2 = sig
  include S2

  val mapM : ('a -> ('b, 'z) t) -> 'a list -> ('b list, 'z) t

  module Syntax : sig

    val (let*) : ('a, 'z) t -> ('a -> ('b, 'z) t) -> ('b, 'z) t

    val (let+) : ('a, 'z) t -> ('a -> 'b) -> ('b, 'z) t

    val return : 'a -> ('a, 'z) t
  end
end

module Make2(M : S2) : T2 with type ('a, 'z) t = ('a, 'z) M.t
