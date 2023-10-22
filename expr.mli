open Utils

module Term : sig
  type term = Var of Var.t | Int of int

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

  val eval : (Var.t * int) list -> t -> int
end

module Flatten : sig
  type flatten = Var.t * Expr.binop * Term.t * Term.t

  type t = flatten

  include Printable with type t := t

  val flatten : Var.t * Expr.t -> t list

  val vars : (Var.t * 'a * Term.t * Term.t) list -> Var.Set.t

  val eval :
    (Var.t * int) list ->
    (Var.t * Expr.binop * Term.t * Term.t) list ->
    (Var.t * int) list
end
