open Misclib
open Zk

module Make
    (F : Curve.F)
    (Protocol : Protocol.S with type f = F.t
                            and type circuit = Circuit.Make(F).t
                            and type qap = QAP.Make(F).t
    )
  : sig

    module Lang : module type of Lang.Make(F)

    val test :
      'a Lang.Expr.t -> Lang.Value.packed String.Map.t -> unit

    val random_test : 'a Lang.Expr.t -> unit
  end

module Make_suites
    (F : Curve.F)
    (Protocol : Protocol.S with type f = F.t
                            and type circuit = Circuit.Make(F).t
                            and type qap = QAP.Make(F).t
    ) : sig end
