open Utils

module type S = sig
  (** element of field *)
  type t

  include Printable with type t := t

  (** 0 *)
  val zero : t

  (** 1 *)
  val one : t

  val of_int : int -> t

  val equal : t -> t -> bool

  val ( + ) : t -> t -> t

  val ( - ) : t -> t -> t

  val ( * ) : t -> t -> t

  val ( / ) : t -> t -> t

  val ( ~- ) : t -> t
end
