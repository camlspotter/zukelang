(** Quadratic Arithmetic Program *)

open Utils

type 'f q = Var.t * 'f Polynomial.t

(* Pinnocio paper says QAP is this triple and a polynomial t(x),
   but here we only take the triple *)
type 'f t = 'f q list Abc.t

module Make(F : Field.S) : sig
  module Poly : Polynomial.S with type f = F.t

  type nonrec q = F.t q

  type nonrec t = F.t t

  include Printable with type t := t

  val of_R1CS : R1CS.t -> t

  val mul_sol : t -> (Var.var * int) list -> Poly.t Abc.t
end

val conv : ('a -> 'b) -> 'a t -> 'b t
