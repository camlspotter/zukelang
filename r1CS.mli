open Utils
open Expr

type row = (Var.t * int) list

type elem = {a : row; b : row; c : row}

val pp_elem : Format.formatter -> elem -> unit

type t = {aa : row list; bb : row list; cc : row list}

include Printable with type t := t

val check : t -> row -> unit

val of_flatten : Var.t list -> Flatten.t -> elem

val of_flatten_list : Var.t list -> Flatten.t list -> t

val transpose : row list -> (Var.t * int list) list
