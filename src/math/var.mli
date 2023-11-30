open Misclib

type var = private string * int [@@deriving yojson]

type t = var [@@deriving yojson]

val compare : t -> t -> int

val pp : t printer

val to_string : t -> string

val make : string -> t

module Set : sig
  include Set.S with type elt = t
  val pp : t printer

  include JSON.Conv.S with type t := t
end

module Map : sig
  include Map.S with type key = t
  val of_set : Set.t -> (var -> 'a) -> 'a t
  val of_list : (var * 'a) list -> 'a t
  val domain : _ t -> Set.t
  val pp : 'a printer -> 'a t printer

  val concat : 'a t -> 'a t -> 'a t
  (** Fails at a collision *)

  val restrict : Set.t -> 'a t -> 'a t

  include JSON.Conv.S1 with type 'a t := 'a t
end

module Infix : sig
  val (#!) : 'a Map.t -> t -> 'a
  (** Query of a varialbe in the map.  Fails if not found *)
end
