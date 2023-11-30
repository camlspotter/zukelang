open Misclib
open Ppx_yojson_conv_lib.Yojson_conv

module type S = sig
  (** element of field *)
  type t

  val pp : t printer

  (** 0 *)
  val zero : t

  val is_zero : t -> bool

  (** 1 *)
  val one : t

  val of_int : int -> t

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

module Int = struct
  (* Not a perfect field but useful *)
  type t = int
  let pp = Format.int
  let (+) = (+)
  let (-) = (-)
  let ( * ) = ( * )
  let (/) = (/)
  let (~-) = (~-)
  let (=) (x : int) y = x = y
  let of_int = Fun.id
  let zero = 0
  let one = 1

  type nonrec int = int [@@deriving yojson]
end
