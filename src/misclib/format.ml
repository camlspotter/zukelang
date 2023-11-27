include Stdlib.Format

let list sep f =
  pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf sep) f

let seq sep f ppf s =
  let rec loop o s =
    match o, s () with
    | None, Seq.Nil -> ()
    | None, Cons (a, at) -> loop (Some a) at
    | Some a, Nil -> f ppf a
    | Some a, Cons (a', at) ->
        f ppf a;
        fprintf ppf sep;
        loop (Some a') at
  in
  loop None s

let f = fprintf

let ef = eprintf

let flip = Fun.flip

let int = pp_print_int

let string = pp_print_string
