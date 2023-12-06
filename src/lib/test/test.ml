open Misclib
open Zk

module Make
    (F : Curve.F)
    (Protocol : Protocol.S with type f = F.t
                            and type circuit = Circuit.Make(F).t
                            and type qap = QAP.Make(F).t
    ) = struct

  module Lang = Lang.Make(F)
  module Comp = Comp.Make(F)
  module Circuit = Circuit.Make(F)
  module QAP = QAP.Make(F)
  module Polynomial = Polynomial.Make(F)

  (* For a given program,

     - Build a circuit, QAP, and keys for proving and verification for the program
     - Execute the program using the given inputs
     - Build a computation witness for the circuit using the inputs
     - Build a ZK proof
     - Verify the proof
  *)
  let test e inputs =
    let open Format in

    ef "\027[37;48;5;34m-------------------------------------------------------------------------- Zukelang test\027[0m@.";
    ef "@[<v2>Program:@ @[%a@]@]@." Lang.Expr.pp e;

    ef "Compiling...@.";
    let comp = Comp.compile e in
    let circuit = comp.circuit in
    ef "@[<v2>Circuit@ @[<v>%a@]@]@." Circuit.pp circuit;

    let qap, _ = QAP.build comp.gates in
    ef "QAP obtained@.";

    let rng = Random.State.make_self_init () in
    let ekey, vkey = Protocol.keygen rng circuit qap in
    ef "Keys generated@.";

    let rec eval () =
      let env_lang = inputs in
      let inputs, env_code = Comp.convert_inputs comp.inputs inputs in

      ef "@[<v2>Inputs:@ @[<v>%a@]@]@."
        (list ",@ " (fun ppf (name, (sec, Lang.Value.Packed (v, _ty), _)) ->
             f ppf "%s : %a = %a" name Lang.pp_security sec Lang.Value.pp v))
      @@ String.Map.bindings inputs;

      (* Note that some variables may be dropped from the final circuit *)
      let env_code =
        let vars = Circuit.vars circuit.gates in
        Var.Map.filter (fun v _ -> Var.Set.mem v vars) env_code
      in

      ef "@[<v2>Flattened inputs@ @[<v>%a@]@]@." (Var.Map.pp F.pp) env_code;

      ef "Evaluating...@.";
      try
        let o = Lang.Eval.eval env_lang e in

        let sol = Comp.Code.eval_list env_code comp.codes in
        o, sol
      with
      | Division_by_zero ->
          eval ()
    in

    let o, sol = eval () in
    ef "Evaluated@.";
    ef "@[<v2>Output:@ @[<v>%a@]@]@." Lang.Value.pp o;
    ef "@[<v2>Witness:@ @[<v>%a@]@]@." (Var.Map.pp F.pp) sol;

    let fs_o = Comp.compile_value e.ty o in
    let fs_sol = List.map (Circuit.Affine.eval sol) comp.result in
    if fs_o <> fs_sol then begin
      ef "A bug of the evaluation detected@.";
      ef "ty : %a@." Lang.Type.pp e.ty;
      ef "components: %d@." @@ Comp.components e.ty;
      ef "fs_o  : @[%a@]@." (list ",@ " F.pp) fs_o;
      ef "fs_sol: @[%a@]@." (list ",@ " F.pp) fs_sol;
      assert false;
    end;

    ef "Proving...@.";
    let proof = Gen.with_rng Protocol.prove qap ekey sol in
    ef "Proven@.";

    ef "Verifying...@.";
    let public =
      Var.Map.filter (fun v _ -> not (Var.Set.mem v circuit.mids)) sol
    in
    ef "@[<v2>Public inputs:@ @[%a@]@]@." (Var.Map.pp F.pp) public;
    assert (Protocol.verify public vkey proof);
    ef "Verified@.@."

  (* For a given program,

     - Build a circuit, QAP, and keys for proving and verification for the program
     - Prepare a random set of inputs and execute the program
     - Build a computation witness for the circuit using the inputs
     - Build a ZK proof
     - Verify the proof
  *)
  let random_test e =
    let open Format in

    ef "\027[37;48;5;34m-------------------------------------------------------------------- Zukelang random test\027[0m@.";
    ef "@[<v2>Program:@ @[%a@]@]@." Lang.Expr.pp e;

    ef "Compiling...@.";
    let comp = Comp.compile e in
    let circuit = comp.circuit in
    ef "@[<v2>Circuit@ @[<v>%a@]@]@." Circuit.pp circuit;

    let qap, _ = QAP.build comp.gates in
    ef "QAP obtained@.";

    let rng = Random.State.make_self_init () in
    let ekey, vkey = Protocol.keygen rng circuit qap in
    ef "Keys generated@.";

    let rec eval () =
      let rng = Random.State.make_self_init () in
      let inputs, env_lang, env_code = Comp.gen_inputs comp.inputs rng in

      ef "@[<v2>Inputs:@ @[<v>%a@]@]@."
        (list ",@ " (fun ppf (name, (sec, Lang.Value.Packed (v, _ty), _)) ->
             f ppf "%s : %a = %a" name Lang.pp_security sec Lang.Value.pp v))
      @@ String.Map.bindings inputs;

      (* Note that some variables may be dropped from the final circuit *)
      let env_code =
        let vars = Circuit.vars circuit.gates in
        Var.Map.filter (fun v _ -> Var.Set.mem v vars) env_code
      in

      ef "@[<v2>Flattened inputs@ @[<v>%a@]@]@." (Var.Map.pp F.pp) env_code;

      ef "Evaluating...@.";
      try
        let o = Lang.Eval.eval env_lang e in

        let sol = Comp.Code.eval_list env_code comp.codes in
        o, sol
      with
      | Division_by_zero ->
          eval ()
    in

    let o, sol = eval () in
    ef "Evaluated@.";
    ef "@[<v2>Output:@ @[<v>%a@]@]@." Lang.Value.pp o;
    ef "@[<v2>Witness:@ @[<v>%a@]@]@." (Var.Map.pp F.pp) sol;

    let fs_o = Comp.compile_value e.ty o in
    let fs_sol = List.map (Circuit.Affine.eval sol) comp.result in
    if fs_o <> fs_sol then begin
      ef "A bug of the evaluation detected@.";
      ef "ty : %a@." Lang.Type.pp e.ty;
      ef "components: %d@." @@ Comp.components e.ty;
      ef "fs_o  : @[%a@]@." (list ",@ " F.pp) fs_o;
      ef "fs_sol: @[%a@]@." (list ",@ " F.pp) fs_sol;
      assert false;
    end;

    ef "Proving...@.";
    let proof = Gen.with_rng Protocol.prove qap ekey sol in
    ef "Proven@.";

    ef "Verifying...@.";
    let public =
      Var.Map.filter (fun v _ -> not (Var.Set.mem v circuit.mids)) sol
    in
    ef "@[<v2>Public inputs:@ @[%a@]@]@." (Var.Map.pp F.pp) public;
    assert (Protocol.verify public vkey proof);
    ef "Verified@.@."
end

module Make_suites
    (F : Curve.F)
    (Protocol : Protocol.S with type f = F.t
                            and type circuit = Circuit.Make(F).t
                            and type qap = QAP.Make(F).t
    ) = struct

  module Test = Make(F)(Protocol)
  module Lang = Lang.Make(F)

  open Lang.Expr.Combinator

  (* I know [x] such that [x^3 + x + 3 = y] *)
  let () =
    Test.random_test
    @@ let_ (input "input" secret ty_field) (fun x -> x * x * x + x + !3)

  (* if *)
  let () =
    Test.random_test
    @@ let_ (input "input" secret ty_field) (fun x -> if_ (x == !0) !1 !2)

  (* $ONE is not used

     gates: v9 = v8 * v8.   No $ONE occurs.

     input_public must be empty!
  *)
  let () =
    Test.random_test
    @@ let_ (input "input" secret ty_field) (fun x -> x * x)

  (* simple pair *)
  let () =
    Test.random_test
    @@ let_ (input "input" secret ty_field) (fun x -> pair (x + !1) (x * x))

  (* complex pair

     $ONE in the code, but is gone from the circuit!
  *)
  let () =
    Test.random_test @@
    let_ (input "input" secret ty_field) @@ fun x ->
    let_ (pair (pair (x + !1) (x * x)) (x * x * x)) @@ fun y ->
    snd (fst y)

  (* return a bool and complex equal *)
  let () =
    Test.random_test @@
    let_ (input "input" secret ty_bool) @@ fun x ->
    let_ (input "input2" secret ty_bool) @@ fun y ->
    pair x y == pair y x

  (* either *)
  let () =
    Test.random_test @@
    let_ (input "input" secret ty_bool) @@ fun x ->
    if_ x (left x ty_bool) (right ty_bool x)

  (* case *)
  let () =
    Test.random_test @@
    let_ (input "input" secret (ty_field +: ty_bool)) @@ fun x ->
    case x (fun i -> i == !0) (fun b -> b)

  (* secret without let *)
  let () =
    Test.random_test @@
    input "input" secret ty_field + !1

  (* compound output *)
  let () =
    Test.random_test @@
    let_ (input "input" secret ty_field) @@ fun x ->
    pair (x + !1) (x + !2)

  (* compound input *)
  let () =
    Test.random_test @@
    let_ (input "input" secret (ty_field *: ty_field)) @@ fun x ->
    fst x + snd x

  (* uint32 + *)
  let () =
    Test.random_test @@
    let_ (input "input" secret ty_uint32) @@ fun x ->
    Uint32.(x + x)

  (* uint32 - *)
  let () =
    Test.random_test @@
    let_ (input "input" secret ty_uint32) @@ fun x ->
    let_ (input "input2" secret ty_uint32) @@ fun y ->
    Uint32.(x - y)

  (* Trans test *)

  let loc = Location.none

  let trans_test e =
    let module Trans = Syntax.Trans.Make(F) in
    match Trans.f e with
    | Ok (Packed e) -> Test.random_test e
    | Error e ->
        Format.ef "%a@." Exn.pp e;
        assert false

  (* I know [x] such that [x^3 + x + 3 = y] *)
  let () =
    trans_test [%expr let x : int = secret "input" in x * x * x + x + 3 ];
    trans_test [%expr let x : int = secret "input" in if x == 0 then 1 else 2 ];
    trans_test [%expr let x : int = secret "input" in x * x ];
    trans_test [%expr let x : int = secret "input" in (x + 1, x * x)];
    trans_test [%expr
      let x : int = secret "input" in
      let y = (x + 1, x * x), x * x * x in
      snd (fst y)
    ];
    trans_test [%expr
      let x : bool = secret "input" in
      let y : bool = secret "input2" in
      (x,y) == (y,x)
    ];
    trans_test [%expr
      let x : bool = secret "input" in
      if x then Either.Left x else Either.Right x
    ];
    trans_test [%expr
      let x : (int * int, bool) Either.t = secret "input" in
      match x with Left x -> fst x * snd x | Right _x -> 1
    ];
    trans_test [%expr secret "input" + 1];
    trans_test [%expr let x : int = secret "input" in (x + 1, x + 2)];
    trans_test [%expr let x : int * int = secret "input" in fst x + snd x]
(*

  (* uint32 + *)
  let () =
    Test.random_test @@
    let_ (input "input" secret ty_uint32) @@ fun x ->
    Uint32.(x + x)

  (* uint32 - *)
  let () =
    Test.random_test @@
    let_ (input "input" secret ty_uint32) @@ fun x ->
    let_ (input "input2" secret ty_uint32) @@ fun y ->
    Uint32.(x - y)
    *)
end
