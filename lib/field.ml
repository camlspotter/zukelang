open Misc

module type S = sig
  (** element of field *)
  type t

  val pp : t printer

  (** 0 *)
  val zero : t

  (** 1 *)
  val one : t

  val of_int : int -> t

  val ( = ) : t -> t -> bool

  val ( + ) : t -> t -> t

  val ( - ) : t -> t -> t

  val ( * ) : t -> t -> t

  val ( / ) : t -> t -> t

  val ( ~- ) : t -> t
end

type 'f s = (module S with type t = 'f)

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
end
