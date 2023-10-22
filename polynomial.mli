open Utils

module Make (A : Field.S) : sig
  type polynomial = A.t list

  type t = polynomial

  include Printable with type t := t

  val zero : 'a list
  val one : A.t list

  val gen : Random.State.t -> A.t list

  val apply : A.t list -> A.t -> A.t
  val normalize : A.t list -> A.t list
  val add : A.t list -> A.t list -> A.t list
  val mul_scalar : A.t -> A.t list -> A.t list
  val neg : A.t list -> A.t list
  val mul : A.t list -> A.t list -> A.t list
  val test_mul : unit -> unit
  val div_rem : A.t list -> A.t list -> A.t list * A.t list
  val lagrange_basis : A.t list -> A.t list list
  val interporate : (A.t * A.t) list -> A.t list

  val test_apply : unit -> unit
  val test_div_rem : unit -> unit
  val test_interporate : unit -> unit
end
