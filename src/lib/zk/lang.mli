open Misclib

module Make(F : Curve.F) : sig

  type security = Public | Secret

  val pp_security : security printer

  module Type : sig
    type uint32

    type _ t =
      | Field : F.t t
      | Bool : bool t
      | Uint32 : uint32 t
      | Pair : 'a t * 'b t -> ('a * 'b) t
      | Either : 'a t * 'b t -> ('a, 'b) Either.t t

    type packed = Packed : _ t -> packed

    val pp : _ t printer

    val equal : 'a t -> 'b t -> ('a, 'b) GADT.eq option
  end

  module Expr : sig
    type 'a t = { desc : 'a desc; ty : 'a Type.t; }

    and 'a desc =
      | Field : F.t -> F.t desc
      | Bool : bool -> bool desc
      | Uint32 : int -> Type.uint32 desc
      | Add : F.t t * F.t t -> F.t desc
      | Sub : F.t t * F.t t -> F.t desc
      | Mul : F.t t * F.t t -> F.t desc
      | Div : F.t t * F.t t -> F.t desc
      | Input : string * security -> 'a desc
      | Not : bool t -> bool desc
      | And : bool t * bool t -> bool desc
      | Or : bool t * bool t -> bool desc
      | If : bool t * 'a t * 'a t -> 'a desc
      | Eq : 'a t * 'a t -> bool desc
      | To_field : 'd t -> F.t desc
      | Let : Var.var * 'a t * 'b t -> 'b desc
      | Var : Var.var -> 'a desc
      | Neg : F.t t -> F.t desc
      | Pair : 'a t * 'b t -> ('a * 'b) desc
      | Fst : ('a * 'b) t -> 'a desc
      | Snd : ('a * 'b) t -> 'b desc
      | Left : 'a t -> ('a, 'e) Either.t desc
      | Right : 'b t -> ('f, 'b) Either.t desc
      | Case : ('a, 'b) Either.t t * Var.var * 'c t * Var.var * 'c t -> 'c desc
      | Add_uint32 : Type.uint32 t * Type.uint32 t -> Type.uint32 desc
      | Sub_uint32 : Type.uint32 t * Type.uint32 t -> Type.uint32 desc

    val ptree : 'a t -> Ptree.t

    val pp : Format.formatter -> 'a t -> unit

    module Combinator : sig
      val ty_field : F.t Type.t
      val ty_bool : bool Type.t
      val ty_uint32 : Type.uint32 Type.t

      val ( *: )  : 'a Type.t -> 'b Type.t -> ('a * 'b) Type.t
      val ( +: )  : 'a Type.t -> 'b Type.t -> ('a, 'b) Either.t Type.t

      val public : security
      val secret : security

      val bool : bool -> bool t
      val field : F.t -> F.t t
      val uint32 : int -> Type.uint32 t
      val ( ! ) : int -> F.t t
      val ( + ) : F.t t -> F.t t -> F.t t
      val ( - ) : F.t t -> F.t t -> F.t t
      val ( ~- ) : F.t t -> F.t t
      val ( * ) : F.t t -> F.t t -> F.t t
      val ( / ) : F.t t -> F.t t -> F.t t
      val not : bool t -> bool t
      val ( && ) : bool t -> bool t -> bool t
      val ( || ) : bool t -> bool t -> bool t
      val if_ : bool t -> 'a t -> 'a t -> 'a t
      val input : string -> security -> 'a Type.t -> 'a t
      val to_field : 'a t -> F.t t
      val let_ : 'a t -> ('a t -> 'b t) -> 'b t
      val ( == ) : 'a t -> 'a t -> bool t
      val pair : 'a t -> 'b t -> ('a * 'b) t
      val fst : ('a * 'b) t -> 'a t
      val snd : ('a * 'b) t -> 'b t
      val left : 'a t -> 'b Type.t -> ('a, 'b) Either.t t
      val right : 'a Type.t -> 'b t -> ('a, 'b) Either.t t
      val case : ('a, 'b) Either.t t -> ('a t -> 'c t) -> ('b t -> 'c t) -> 'c t

      module Uint32 : sig
        val (+) : Type.uint32 t -> Type.uint32 t -> Type.uint32 t
        val (-) : Type.uint32 t -> Type.uint32 t -> Type.uint32 t
      end
    end
  end

  module Value : sig
    type _ t =
      | Field : F.t -> F.t t
      | Bool : bool -> bool t
      | Uint32 : int -> Type.uint32 t
      | Pair : 'a t * 'b t -> ('a * 'b) t
      | Left : 'a t -> ('a, 'c) Either.t t
      | Right : 'b t -> ('d, 'b) Either.t t

    type packed = Packed : 'a t * 'a Type.t -> packed

    val unpack : 'a Type.t -> packed -> 'a t option

    val pp : _ t printer

    val gen : 'a Type.t -> 'a t Gen.t
  end

  module Env : sig
    type t = Value.packed Var.Map.t

    val add : Var.t -> 'a Type.t -> 'a Value.t -> t -> t

    val find : Var.t -> 'a Type.t -> t -> 'a Value.t
  end

  module Eval : sig
    val eval : Value.packed String.Map.t -> 'a Expr.t -> 'a Value.t
  end
end
