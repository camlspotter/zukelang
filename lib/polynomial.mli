open Misc

type 'f polynomial = 'f list

type 'f t = 'f polynomial

module type S = sig
  type f

  type nonrec polynomial = f polynomial

  type t = polynomial

  val pp : t printer

  val zero : t

  val one : t

  val gen : t Gen.t

  val apply : t -> f -> f
  (** [apply f x] computes $f(x)$ *)

  val normalize : t -> t

  val add : t -> t -> t

  val sum : t list -> t

  val mul_scalar : f -> t -> t

  val neg : t -> t

  val mul : t -> t -> t
  (** Beware, $O(N^2)$! *)

  val div_rem : t -> t -> t * t

  val lagrange_basis : f list -> t list
  (** https://en.wikipedia.org/wiki/Lagrange_polynomial

      For $x_0, .., x_n$, returns $l_0(x); ..; l_n(x)$
      such that

      $l_j(x_j) = 1$
      $l_j(x_i) = 0$ for $i \neq j$
  *)

  val interpolate : (f * f) list -> t
  (** For $\{(x_i,y_i)\}$, returns a polynomial $f$ such that

      $f(x_i) = y_i$
  *)

  val z : f list -> t
  (** [z fs] is a minimal polynomial (except zero) which returns 0s
      at all the point of [fs].
  *)

  val degree : t -> int
  (** The highest of the degrees of the polynomial's monomials with non-zero coefficients.
      The degree of $3x^9 + 4x^8 + 3^x^4 + 1$ is $9$.
  *)

  val is_zero : t -> bool

  val equal : t -> t -> bool

  module Infix : sig
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( *$ ) : f -> t -> t
    val ( /% ) : t -> t -> t * t
    val ( ~- ) : t -> t
  end
end

module Make (F : Field.S) : S with type f = F.t

val conv : ('a -> 'b)  -> 'a t -> 'b t
(** Conversion of the coefficients *)
