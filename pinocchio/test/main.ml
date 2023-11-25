open Utils

let () =
  let module Circuit = Circuit.Make(Q) in
  Circuit.test ()

let () = Pinocchio.test ()

module C = Ecp.Bls12_381
module F = C.Fr
module Lang = Zukelang.Lang.Make(F)
module Comp = Zukelang.Comp.Make(F)
module Circuit = Circuit.Make(F)
module QAP = QAP.Make(F)
module Pinocchio = Pinocchio.Make(C)

let test e =
  let open Format in

  ef "code: %a@." Lang.pp e;

  let _output, Comp.{ gates; inputs; mids; outputs; codes } = Comp.compile e in
  let circuit =
    let inputs = Var.Map.bindings inputs in
    let inputs_public =
      List.filter_map (function
          | (_, (Lang.Secret, _)) -> None
          | (v, _) -> Some v) inputs
    in
    let output = outputs in
    let input = Var.Set.of_list inputs_public in
    Circuit.{ gates; input; output; mids }
  in
  ef "circuit @[<v>%a@]@." Circuit.pp circuit;

  let qap, _ = QAP.build gates in
  ef "qap done@.";

  let ekey, vkey = Pinocchio.ZK.keygen circuit qap in
  ef "keygen done@.";

  let rng = Random.State.make_self_init () in

  let rec eval () =
    let env =
      Var.Map.mapi (fun v (_, ty) ->
          if v = Circuit.one then F.one
          else Comp.gen_value ty rng) inputs
    in
    ef "inputs @[<v>%a@]@." (Var.Map.pp F.pp) env;
    match Comp.Code.eval_list env codes with
    | exception Division_by_zero ->
        ef "Division by zero. Re-evaluating...@.";
        eval ()
    | sol -> sol
  in

  let sol = eval () in
  ef "evaluated@.";
  ef "sol: @[<v>%a@]@." (Var.Map.pp F.pp) sol;

  let proof = Pinocchio.ZK.prove qap ekey sol in
  ef "proven@.";

  ef "verifying@.";
  let public =
    Var.Map.filter (fun v _ -> not (Var.Set.mem v circuit.mids)) sol
  in
  ef "public: @[%a@]@." (Var.Map.pp F.pp) public;
  assert (Pinocchio.ZK.verify public vkey proof)

let () =
  let open Lang.S in
  let e =
    let x = Lang.var () in
    let_ x (input secret ty_field) (if_ (var x == !0) !1 !2)
  in
  test e
