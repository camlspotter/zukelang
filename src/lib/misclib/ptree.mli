(** OCaml untyped AST *)

type t = Parsetree.expression

val var : string -> t

val pvar : string -> Parsetree.pattern

val int : string -> t

val string : string -> t

val pp : Format.formatter -> t -> unit
