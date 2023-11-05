open Utils

let () =
  let module Circuit = Circuit.Make(Q) in
  Circuit.test ()

let () = Pinocchio.test ()
