open Misclib

module type S = sig
  type f

  type circuit

  type qap

  type pkey [@@deriving yojson] (** Proving key *)

  type vkey [@@deriving yojson] (** Verificaiton key *)

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
     end)
    (Protocol : S with type f = F.t
                   and type circuit = Circuit.Make(F).t
                   and type qap = QAP.Make(F).t
    ) = struct

  module Lang = Lang.Make(F)
  module Comp = Comp.Make(F)
  module Circuit = Circuit.Make(F)
  module QAP = QAP.Make(F)

  let test e =
    let open Format in

    ef "Testing code: %a@." Lang.Expr.pp e;

    let comp = Comp.compile e in
    let circuit = comp.circuit in

    ef "circuit @[<v>%a@]@." Circuit.pp circuit;

    let qap, _ = QAP.build comp.gates in
    ef "qap done@.";

    let rng = Random.State.make_self_init () in
    let ekey, vkey = Protocol.keygen rng circuit qap in
     ef "keygen done@.";

    let rng = Random.State.make_self_init () in

    let rec eval () =
      let env =
        Var.Map.mapi (fun v (_, ty) ->
            if v = Circuit.one then F.one
            else Comp.gen_value ty rng) comp.inputs
      in
      ef "inputs @[<v>%a@]@." (Var.Map.pp F.pp) env;
      match Comp.Code.eval_list env comp.codes with
      | exception Division_by_zero ->
          ef "Division by zero. Re-evaluating...@.";
          eval ()
      | sol -> sol
    in

    let sol = eval () in
    ef "evaluated@.";
    ef "sol: @[<v>%a@]@." (Var.Map.pp F.pp) sol;

    let rng = Random.State.make_self_init () in
    let proof = Protocol.prove rng qap ekey sol in
    ef "proven@.";

    ef "verifying@.";
    let public =
      Var.Map.filter (fun v _ -> not (Var.Set.mem v circuit.mids)) sol
    in
    ef "public: @[%a@]@." (Var.Map.pp F.pp) public;
    assert (Protocol.verify public vkey proof);
    ef "verified!!!@.@."
end
