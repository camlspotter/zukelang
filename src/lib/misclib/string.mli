include module type of struct include Stdlib.String end

module Set : Set.S with type elt = string

module Map : Map.S with type key = string
