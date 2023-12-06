exception Type_error of Location.report

let () =
  Misclib.Exn.register_printer @@ function
  | Type_error report -> Some (fun ppf -> Location.print_report ppf report)
  | _ -> None

let expression extend_env (e : Ppxlib.Parsetree.expression) =
  let source_file =
    let Location.{ loc_start; _ } = e.pexp_loc in
    loc_start.pos_fname
  in
  let str = [ Parsetree.{ pstr_desc= Pstr_eval (e, []); pstr_loc = Location.none } ] in
  Compile_common.with_info
    ~native:false
    ~tool_name:"ocamlc"
    ~source_file
    ~output_prefix:"dummy"
    ~dump_ext:"dummy_ext" @@ fun info ->
  let info = { info with env = extend_env info.env } in
  try
    Ok (Compile_common.typecheck_impl info str)
  with
  | exn ->
      match Location.error_of_exn exn with
      | Some (`Ok error) -> Error (Type_error error)
      | Some `Already_displayed -> assert false
      | None -> raise exn
