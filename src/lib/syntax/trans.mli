open Misclib
open Zk

module Make(F : Curve.F) : sig
  module Lang : module type of Lang.Make(F)

  exception Illegal of Warnings.loc * string

  val f : Parsetree.expression -> Lang.Expr.packed Exn.result
end
