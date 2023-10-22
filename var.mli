open Utils

type var = private string

type t = var

val compare : t -> t -> int

include Printable with type t := t

val of_string : string -> var

val to_string : var -> string

module Set : Set.S with type elt = t
