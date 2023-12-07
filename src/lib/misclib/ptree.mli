(** OCaml untyped AST *)

open Astlib.Ast_414

type t = Parsetree.expression

val var : string -> t

val pvar : string -> Parsetree.pattern

val int : ?suffix:char -> string -> t

val string : string -> t

val pp : Format.formatter -> t -> unit
