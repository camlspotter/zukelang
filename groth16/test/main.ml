open Utils

module C = Ecp.Bls12_381
module F = C.Fr
module Lang = Zukelang.Lang.Make(F)
module Comp = Zukelang.Comp.Make(F)
module Circuit = Circuit.Make(F)
module QAP = QAP.Make(F)

module Groth16 = Groth16.Make(C)

let test e =
  let open Format in

  ef "code: %a@." Lang.pp e;

  let comp = Comp.compile e in
  let circuit = comp.circuit in

  ef "circuit @[<v>%a@]@." Circuit.pp circuit;

  let qap, _ = QAP.build comp.gates in
  ef "qap done@.";

  let rng = Gen.init_auto () in
  let ekey, vkey = Groth16.keygen rng circuit qap in
  ef "keygen done@.";

  let rng = Gen.init_auto () in

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

  let rng = Gen.init_auto () in
  let proof = Groth16.prove rng qap ekey sol in
  ef "proven@.";

  ef "verifying@.";
  let public =
    Var.Map.filter (fun v _ -> not (Var.Set.mem v circuit.mids)) sol
  in
  ef "public: @[%a@]@." (Var.Map.pp F.pp) public;
  assert (Groth16.verify public vkey proof)

let () =
  let open Lang.S in
  let e =
    let x = Lang.var () in
    let_ x (input secret ty_field) (if_ (var x == !0) !1 !2)
  in
  test e
