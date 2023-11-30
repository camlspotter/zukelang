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

    let rec eval () =
      let rng = Random.State.make_self_init () in
      let inputs, env_lang, env_code = Comp.gen_inputs comp.inputs rng in

      ef "Inputs: @[<v>%a@]@."
        (list ",@ " (fun ppf (name, (sec, Lang.Value.Packed (v, _ty), _)) ->
             f ppf "%s : %a = %a" name Lang.pp_security sec Lang.Value.pp v))
      @@ String.Map.bindings inputs;

      (* Note that some variables may be dropped from the final circuit *)
      let env_code =
        let vars = Circuit.vars circuit.gates in
        Var.Map.filter (fun v _ -> Var.Set.mem v vars) env_code
      in

      ef "Inputs_code @[<v>%a@]@." (Var.Map.pp F.pp) env_code;

      try
        let o = Lang.Eval.eval env_lang e in

        let sol = Comp.Code.eval_list env_code comp.codes in
        o, sol
      with
      | Division_by_zero ->
          eval ()
    in

    let o, sol = eval () in
    ef "evaluated@.";
    ef "o: @[<v>%a@]@." Lang.Value.pp o;
    ef "sol: @[<v>%a@]@." (Var.Map.pp F.pp) sol;

    let fs_o = Comp.compile_value e.ty o in
    let fs_sol = List.map (Circuit.Affine.eval sol) comp.result in
    if fs_o <> fs_sol then begin
      ef "ty : %a@." Lang.Type.pp e.ty;
      ef "components: %d@." @@ Comp.components e.ty;
      ef "fs_o  : @[%a@]@." (list ",@ " F.pp) fs_o;
      ef "fs_sol: @[%a@]@." (list ",@ " F.pp) fs_sol;
      assert false;
    end;

    let proof = Gen.with_rng Protocol.prove qap ekey sol in
    ef "proven@.";

    ef "verifying@.";
    let public =
      Var.Map.filter (fun v _ -> not (Var.Set.mem v circuit.mids)) sol
    in
    ef "public: @[%a@]@." (Var.Map.pp F.pp) public;
    assert (Protocol.verify public vkey proof);
    ef "verified!!!@.@."
end
