open Misclib

module type S = sig
  type t

  val pp : t Misclib.printer
  val zero : t
  val is_zero : t -> bool
  val one : t
  val of_int : int -> t
  val of_z : Z.t -> t
  val ( = ) : t -> t -> bool
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val ( ~- ) : t -> t

  include JSON.Conv.S with type t := t
end

module type COMPARABLE = sig
  include S
  val compare : t -> t -> int
end
