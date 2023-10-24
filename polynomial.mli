open Utils

module type S = sig
  type f

  type polynomial = f list

  type t = polynomial

  include Printable with type t := t

  val zero : 'a list

  val one : f list

  val gen : Random.State.t -> f list

  val apply : f list -> f -> f
  (** Compute f(x) for the specified value of x *)

  val normalize : f list -> f list

  val add : f list -> f list -> f list

  val mul_scalar : f -> f list -> f list

  val neg : f list -> f list

  val mul : f list -> f list -> f list

  val div_rem : f list -> f list -> f list * f list

  val lagrange_basis : f list -> f list list

  val interporate : (f * f) list -> f list
end

module Make (A : Field.S) : S with type f = A.t
