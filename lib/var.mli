open Misc

type var = private string

type t = var

val compare : t -> t -> int

val pp : t printer

val of_string : string -> var

val to_string : var -> string

module Set : sig
  include Set.S with type elt = t
  val pp : t printer
end

module Map : sig
  include Map.S with type key = t
  val of_set : Set.t -> (var -> 'a) -> 'a t
  val of_list : (var * 'a) list -> 'a t
  val domain : _ t -> Set.t
  val pp : 'a printer -> 'a t printer

  val concat : 'a t -> 'a t -> 'a t
  (** Fails at a collision *)
end

module Infix : sig
  val (#!) : 'a Map.t -> t -> 'a
  (** Query of a varialbe in the map.  Fails if not found *)
end
