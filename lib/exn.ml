open Error

type t = exn

let to_string = Printexc.to_string

let catch f = try Ok (f ()) with exn -> Error (Exn exn)

let catch_as_string f = try Ok (f ()) with exn -> Error (to_string exn)
