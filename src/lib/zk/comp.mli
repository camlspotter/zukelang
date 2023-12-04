open Misclib

module Make(F : Curve.F) : sig

  module Circuit : module type of Circuit.Make(F)
  module Lang : module type of Lang.Make(F)

  module Code : sig
    type code =
      | Mul of code * code
      | Div of code * code
      | Not of code
      | Or of code * code
      | Affine of Circuit.Affine.t
      | Eq of code * code
      | If of code * code * code

    type t = code

    module Combinator : sig
      val ( * ) : t -> t -> t
      val ( / ) : t -> t -> t
      val not : t -> t
      val ( || ) : t -> t -> t
      val ( !& ) : Circuit.Affine.t -> t
      val ( == ) : t -> t -> t
      val if_ : t -> t -> t -> t
    end

    val pp : Format.formatter -> t -> unit

    val vars : t -> Var.Set.t

    type env = F.t Var.Map.t

    val eval : env -> t -> F.t

    val eval_list : env -> (Var.var * t) list -> env
  end

  val components : 'a Lang.Type.t -> int

  val compile_value : 'a Lang.Type.t -> 'a Lang.Value.t -> F.t list

  type input_type = Lang.security * Lang.Type.packed * Var.t list

  type input_value = Lang.security * Lang.Value.packed * (Var.t * F.t) list

  type t =
    { gates : Circuit.Gate.Set.t;
      inputs : input_type String.Map.t;
      inputs_vars : Lang.security Var.Map.t;
      mids : Var.Set.t;
      outputs : Var.Set.t;
      codes : (Var.var * Code.code) list;
      result : Circuit.Affine.t list;
      circuit : Circuit.t
    }

  val compile : 'a Lang.Expr.t -> t

  val gen_inputs :
    input_type String.Map.t ->
    (input_value String.Map.t
     * Lang.Value.packed String.Map.t
     * Code.env) Gen.t

  val convert_inputs :
    input_type String.Map.t ->
    Lang.Value.packed String.Map.t ->
    input_value String.Map.t * Code.env

  val test : 'a Lang.Expr.t -> unit
end

val test : unit -> unit
