open Misclib

type t = float * float [@@deriving yojson]

let zero = 0.0, 0.0
let ( + ) (r1, i1) (r2, i2) = (r1 +. r2, i1 +. i2)
let ( - ) (r1, i1) (r2, i2) = (r1 -. r2, i1 -. i2)
let ( * ) (r1, i1) (r2, i2) = (r1 *. r2 -. i1 *. i2, r1 *. i2 +. r2 *. i1)
let ( / ) (r1, i1) (r2, i2) =
  (* $(a + bi) / (c + di) = (a + bi)(c - di) / (c^2 + d^2 )$
     $= ac + bd + (bc - ad)i / (c^2 - d^2) $ *)
  let c2d2 = r2 *. r2 +. i2 *. i2 in
  ((r1 *. r2 +. i1 *. i2) /. c2d2, (i1 *. r2 -. r1 *. i2) /. c2d2 )

let (~-) (r, i) = (-. r, -. i)

let is_zero (r, i) = r = 0.0 && i = 0.0

let (=) (r1, i1) (r2, i2) = r1 = r2 && i1 = i2

let (=.) =
  let (=.) f1 f2 = Float.abs (f1 -. f2) < 0.00001 in
  fun (r1, i1) (r2, i2) -> r1 =. r2 && i1 =. i2

let of_int i = (float i, 0.)

let one = (1.0, 0.)

let polar ~r ~t = r *. cos t, r *. sin t
let zeta n i = polar ~r:1.0 ~t:(Float.pi *. 2.0 /. float n *. float i)

let pp ppf (r,i) = Format.f ppf "(%f + %fi)" r i

let sum xs = List.fold_left (+) zero xs

let () =
  assert ((1.0, 2.0) * (3.0, 4.0) = (-5.0, 10.0));
  assert ((1.0, 1.0) / (2.0, 1.0) = (0.6, 0.2))
