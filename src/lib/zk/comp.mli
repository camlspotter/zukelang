open Misclib

module Make(F : sig
    include Field.COMPARABLE
    val gen : t Gen.t
    val ( ** ) : t -> Z.t -> t
    val order : Z.t
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

    module Combinator : sig
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

    val eval : env -> t -> F.t

    val eval_list : env -> (Var.var * t) list -> env
  end

  val components : 'a Lang.Make(F).Type.t -> int

  val compile_value : 'a Lang.Make(F).Type.t -> 'a Lang.Make(F).Value.t -> F.t list

  type input_type = Lang.Make(F).security * Lang.Make(F).Type.packed * Var.t list

  type input_value = Lang.Make(F).security * Lang.Make(F).Value.packed * (Var.t * F.t) list

  type t =
    { gates : Circuit.Make(F).Gate.Set.t;
      inputs : input_type String.Map.t;
      inputs_vars : Lang.Make(F).security Var.Map.t;
      mids : Var.Set.t;
      outputs : Var.Set.t;
      codes : (Var.var * Code.code) list;
      result : Circuit.Make(F).Affine.t list;
      circuit : Circuit.Make(F).t
    }

  val compile : 'a Lang.Make(F).Expr.t -> t

  val gen_inputs :
    input_type String.Map.t ->
    (input_value String.Map.t
     * Lang.Make(F).Value.packed String.Map.t
     * Code.env) Gen.t

  val convert_inputs :
    input_type String.Map.t ->
    Lang.Make(F).Value.packed String.Map.t ->
    input_value String.Map.t * Code.env

  val test : 'a Lang.Make(F).Expr.t -> unit
end

val test : unit -> unit
