type 'a t = {a : 'a; b : 'a; c : 'a}

let pp pp_t ppf {a; b; c} =
  let open Format in
  fprintf ppf "{ @[<v>" ;
  fprintf ppf "a: @[%a@];@ " pp_t a ;
  fprintf ppf "b: @[%a@];@ " pp_t b ;
  fprintf ppf "c: @[%a@];@ " pp_t c ;
  fprintf ppf "@] }"
