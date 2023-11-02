open Utils

let () = Pairing.test ()

let () =
  let module Circuit = Circuit.Make(Q) in
  Circuit.test ()

let () = Pinocchio.test ()
