include Field.S with type t = float * float [@@deriving yojson]

val (=.) : t -> t -> bool
(** Nearly equal *)

val polar : r: float -> t : float -> t
val zeta : int (* N *) -> int (* i *) -> t
(** $\zeta^i_N$ *)

val sum : t list -> t
