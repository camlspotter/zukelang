open Misclib

module type S = sig

  type f
  (** Type of the prime field element *)

  type circuit

  type qap

  type pkey [@@deriving yojson]
  (** Proving key *)

  type vkey [@@deriving yojson]
  (** Verificaiton key *)

  type proof [@@deriving yojson]

  val keygen : Gen.rng -> circuit -> qap -> pkey * vkey
  (** Key generation *)

  val prove : Gen.rng -> qap -> pkey -> f Var.Map.t -> proof
  (** Obtain a proof of the computation *)

  val verify : f Var.Map.t -> vkey -> proof -> bool
  (** Verify the computation proof *)
end

module Test
    (F : sig
       include Field.COMPARABLE
       val gen : t Gen.t
       val ( ** ) : t -> Z.t -> t
       val order : Z.t
     end)
    (Protocol : S with type f = F.t
                   and type circuit = Circuit.Make(F).t
                   and type qap = QAP.Make(F).t
    )
  : sig
    val test :
      'a Lang.Make(F).Expr.t -> Lang.Make(F).Value.packed String.Map.t -> unit

    val random_test : 'a Lang.Make(F).Expr.t -> unit
  end

module Test_suites
    (F : sig
       include Field.COMPARABLE
       val gen : t Gen.t
       val ( ** ) : t -> Z.t -> t
       val order : Z.t
     end)
    (Protocol : S with type f = F.t
                   and type circuit = Circuit.Make(F).t
                   and type qap = QAP.Make(F).t
    ) : sig end
