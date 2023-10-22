open Utils

module Term : sig
  type term = Var of string | Int of int

  type t = term

  include Printable with type t := t
end

module Expr : sig
  type binop = Add | Mul

  type expr = Term of Term.t | BinApp of binop * expr * expr

  type t = expr

  include Printable with type t := t

  val var : string -> t

  val int : int -> t

  val mul : t -> t -> t

  val add : t -> t -> t

  val eval : (string * int) list -> t -> int
end

module Flatten : sig
  type flatten = string * Expr.binop * Term.t * Term.t

  type t = flatten

  include Printable with type t := t

  val flatten : string * Expr.t -> t list

  val vars' : Var.Set.t -> string * 'a * Term.t * Term.t -> Var.Set.t

  val vars : (string * 'a * Term.t * Term.t) list -> Var.Set.t

  val eval_ : (string * int) list -> Expr.binop * Term.t * Term.t -> int option

  val eval :
    (string * int) list ->
    (string * Expr.binop * Term.t * Term.t) list ->
    (string * int) list
end
