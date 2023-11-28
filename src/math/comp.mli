open Misclib

module Make(F : sig
    include Field.COMPARABLE
    val gen : t Gen.t
  end) : sig

  module Code : sig
    type code =
      | Mul of code * code
      | Div of code * code
      | Not of code
      | Or of code * code
      | Affine of Circuit.Make(F).Affine.t
      | Eq of code * code
      | If of code * code * code

    type t = code

    module C : sig
      val ( * ) : t -> t -> t
      val ( / ) : t -> t -> t
      val not : t -> t
      val ( || ) : t -> t -> t
      val ( !& ) : Circuit.Make(F).Affine.t -> t
      val ( == ) : t -> t -> t
      val if_ : t -> t -> t -> t
    end

    val pp : Format.formatter -> t -> unit

    val vars : t -> Var.Set.t

    type env = F.t Var.Map.t

    val convert_env : Lang.Make(F).Env.t -> env

    val eval : env -> t -> F.t

    val eval_list : env -> (Var.var * t) list -> env
  end

  type ty = Field | Bool

  val gen_value : ty -> F.t Gen.t

  type t =
    { gates : Circuit.Make(F).Gate.Set.t;
      inputs : (Lang.Make(F).security * ty) Var.Map.t;
      mids : Var.Set.t;
      outputs : Var.Set.t;
      codes : (Var.var * Code.code) list;
      result : Circuit.Make(F).Affine.t list;
      circuit : Circuit.Make(F).t
    }

  val compile : 'a Lang.Make(F).Expr.t -> t

  val test : 'a Lang.Make(F).Expr.t -> unit
end

val test : unit -> unit
