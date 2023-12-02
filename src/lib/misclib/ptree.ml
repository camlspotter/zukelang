open Ppxlib_ast.Ast_helper

type t = Astlib.Ast_414.Parsetree.expression

let var name = Exp.ident { txt= Longident.Lident name; loc= Location.none }

let pvar name = Pat.var {txt= name; loc= Location.none}

let int ?suffix s = Exp.constant @@ Const.integer ?suffix s

let string s = Exp.constant @@ Const.string s

let pp = Ppxlib_ast.Pprintast.expression
