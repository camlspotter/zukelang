type t = exn

type printer = t -> (Format.t -> unit) option

let printers : printer list ref = ref []

let register_printer f = printers := f :: !printers

let pp ppf e =
  let rec loop = function
    | [] -> Format.string ppf (Printexc.to_string e)
    | p::ps ->
        (match p e with
         | None -> loop ps
         | Some f -> f ppf)
  in
  loop !printers

let to_string e = Format.asprintf "%a" pp e

type exn += String of string

let () =
  register_printer @@ function
  | String s -> Some (fun ppf -> Format.string ppf s)
  | _ -> None

type 'a result = ('a, t) Result.t

module Monad = Monad.Make(struct
    type nonrec 'a t = 'a result
    let bind = Result.bind
    let map = Result.map
    let return x = Ok x
  end)

let catch f = try Ok (f ()) with exn -> Error exn

let get_ok = function
  | Ok x -> x
  | Error e -> raise e
