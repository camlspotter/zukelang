open Utils

module Make(C : Ecp.CURVE) : Protocol.S
  with type f = C.Fr.t
   and type circuit = Circuit.Make(C.Fr).t
   and type qap = QAP.Make(C.Fr).t
