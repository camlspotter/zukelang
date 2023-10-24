open Utils

module PQ : Polynomial.S with type f = Q.t

type q = Var.t * PQ.t

val pp_q : q printer

type t = { a : q list; b : q list; c : q list }

include Printable with type t := t

val of_R1CS_rows : R1CS.row list -> q list

val of_R1CS : R1CS.t -> t
