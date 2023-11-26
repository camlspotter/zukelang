open Misc

type t = float * float [@@deriving yojson]

val zero : t
val is_zero : t -> bool
val one : t
val of_int : int -> t

val (+) : t -> t -> t
val (-) : t -> t -> t
val ( * ) : t -> t -> t
val (/) : t -> t -> t

val (~-) : t -> t

val (=) : t -> t -> bool

val (=.) : t -> t -> bool
(** Nearly equal *)

val polar : r: float -> t : float -> t
val zeta : int (* N *) -> int (* i *) -> t
(** $\zeta^i_N$ *)

val sum : t list -> t

val pp : t printer
