include Stdlib.Seq

let mapi f t =
  let rec aux n t =
    fun () ->
      match t () with
      | Nil -> Nil
      | Cons (x, t) ->
          let x = f n x in
          let t = aux (n+1) t in
          Cons (x, t)
  in
  aux 0 t
