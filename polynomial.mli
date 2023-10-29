open Utils

type 'f polynomial = 'f list

type 'f t = 'f polynomial

module type S = sig
  type f

  type nonrec polynomial = f polynomial

  type t = polynomial

  include Printable with type t := t

  val zero : t

  val one : t

  val gen : Random.State.t -> t

  val apply : t -> f -> f
  (** Compute f(x) for the specified value of x *)

  val normalize : t -> t

  val add : t -> t -> t

  val sum : t list -> t

  val mul_scalar : f -> t -> t

  val neg : t -> t

  val mul : t -> t -> t

  val div_rem : t -> t -> t * t

  val lagrange_basis : f list -> t list
  (** https://en.wikipedia.org/wiki/Lagrange_polynomial

      For [x_0; ..; x_n], returns [ l_0(x); ..; l_n(x) ]
      where

      l_j(x_j) = 1
      l_j(x_i) = 0 for i <> j
  *)

  val interpolate : (f * f) list -> t
  (** For [(x_0,y_0); ..; (x_n,y_n)], returns a polynomial p such that

      p(x_i) = y_i
  *)

  val z : f list -> t
  (** [z fs] is a minimal polynomial (except zero) which returns 0s
      at all the point of [fs].

      [fs] must be distinct but there is no check for it.
  *)

  val degree : t -> int

  val is_zero : t -> bool

  module Infix : sig
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( ~- ) : t -> t
    val ( * ) : t -> t -> t
    val ( *$ ) : f -> t -> t
    val ( /% ) : t -> t -> t * t
  end
end

module Make (A : Field.S) : S with type f = A.t

val conv : ('a -> 'b)  -> 'a t -> 'b t
