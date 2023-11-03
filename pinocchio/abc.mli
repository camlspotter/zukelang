open Utils

type 'a t = {a : 'a; b : 'a; c : 'a}

val pp : 'a printer -> 'a t printer

val map : ('a -> 'b) -> 'a t -> 'b t

val split : 'a t list -> 'a list t
(** Analogy : List.split : ('a * 'b) list -> 'a list * 'b list *)
