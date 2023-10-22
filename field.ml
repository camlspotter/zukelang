open Utils

module type S = sig

  type t
  (** element of field *)

  include Printable with type t := t

  val zero : t
  (** 0 *)

  val one : t
  (** 1 *)

  val of_int : int -> t

  val equal : t -> t -> bool

  val (+) : t -> t -> t

  val (-) : t -> t -> t

  val ( * ) : t -> t -> t

  val (/) : t -> t -> t

  val (~-) : t -> t
end
