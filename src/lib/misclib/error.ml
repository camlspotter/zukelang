type error = ..

type t = error

let printers = ref []

let to_string e =
  let rec loop = function
    | [] -> "no error printer"
    | p::ps ->
        (match p e with
         | None -> loop ps
         | Some s -> s)
  in
  loop !printers

let register_printer f = printers := f :: !printers

type error += Exn of exn

let () =
  register_printer (function
      | Exn e -> Some (Printexc.to_string e)
      | _ -> None)

type error += String of string

let () =
  register_printer (function
      | String s -> Some s
      | _ -> None)

type nonrec 'a result = ('a, error) result

module Monad = Monad.Make(struct
    type nonrec 'a t = 'a result
    let bind = Result.bind
    let map = Result.map
    let return x = Ok x
  end)

exception Error of error

let raise e =
  match e with
  | Exn exn -> raise exn
  | _ -> raise (Error e)
