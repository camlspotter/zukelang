open Utils

type var = private string

type t = var

val compare : t -> t -> int

include Printable with type t := t

val of_string : string -> var

val to_string : var -> string

module Set : sig
  include Set.S with type elt = t
  val pp : t printer
end

module Map : sig
  include Map.S with type key = t
  val of_set : Set.t -> (var -> 'a) -> 'a t
  val domain : _ t -> Set.t
end
