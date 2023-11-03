open Utils
open Expr

type row = (Var.t * int) list

type elem = row Abc.t

val pp_elem : Format.formatter -> elem -> unit

type t = row list Abc.t

include Printable with type t := t

val check : t -> row -> unit

val of_flatten : Var.t list -> Flatten.t -> elem

val of_flatten_list : Var.t list -> Flatten.t list -> t

val transpose : row list -> (Var.t * int list) list
