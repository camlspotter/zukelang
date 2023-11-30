open Zk

module Make(C : Curve.S) : sig
  (** Verified computation without ZK *)
  module NonZK : Protocol.S
    with type f = C.Fr.t
     and type circuit = Circuit.Make(C.Fr).t
     and type qap = QAP.Make(C.Fr).t

  (** Verified computation with ZK *)
  module ZK : Protocol.S
    with type f = C.Fr.t
     and type circuit = Circuit.Make(C.Fr).t
     and type qap = QAP.Make(C.Fr).t
end
