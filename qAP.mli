open Utils

module PQ : Polynomial.S with type f = Q.t

type q = Var.t * PQ.t

type t = q list Abc.t

include Printable with type t := t

val of_R1CS : R1CS.t -> t

val mul_sol : t -> (Var.var * int) list -> PQ.polynomial Abc.t
