open Utils

type var = string

type t = var

val compare : t -> t -> int

include Printable with type t := t

module Set : Set.S with type elt = t
