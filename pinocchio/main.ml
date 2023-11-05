open Utils
open Pinocchio

let () =
  let module Circuit = Circuit.Make(Q) in
  Circuit.test ()

let () = Zk.test ()
