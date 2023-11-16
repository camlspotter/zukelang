open Misc

type 'f polynomial = 'f list

type 'f t = 'f polynomial

module type S = sig
  type f

  type nonrec polynomial = f polynomial

  type t = polynomial

  val pp : t printer

  val zero : t

  val one : t

  val gen : int Gen.t -> t Gen.t

  val apply : t -> f -> f

  val normalize : t -> t

  val add : t -> t -> t

  val sum : t list -> t

  val mul_scalar : f -> t -> t

  val neg : t -> t

  val mul : t -> t -> t

  val div_rem : t -> t -> t * t

  val lagrange_basis : f list -> t list

  val interpolate : (f * f) list -> t

  val z : f list -> t

  val degree : t -> int

  val is_zero : t -> bool

  val equal : t -> t -> bool

  module Infix : sig
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( *$ ) : f -> t -> t
    val ( /% ) : t -> t -> t * t
    val ( ~- ) : t -> t
  end

  val test : unit -> unit
end

module Make (A : Field.S) : S with type f = A.t = struct
  type f = A.t

  type polynomial = f list (* a + bx + cx^2 + dx^3 *)

  type t = polynomial

  let zero = [] (* 0 *)

  let one = [A.one] (* 1 *)

  let pp ppf p =
    let open Format in
    match p with
    | [] -> A.pp ppf A.zero
    | _ ->
        list " + "
          (fun ppf (i, p) ->
            if i = 0 then A.pp ppf p
            else if i = 1 then f ppf "%a x" A.pp p
            else f ppf "%a x^%d" A.pp p i)
          ppf
        @@ List.mapi (fun i a -> (i, a)) p

  (* f(x) *)
  let apply f x =
    fst
    @@ List.fold_left
         (fun (acc, xi) a -> A.(acc + (a * xi), xi * x))
         (A.zero, A.one)
         f

  let test_apply () =
    (* 1 + 2x + 3x^2 + 4x^3  for x = 2 = 49 *)
    let q = A.of_int in
    assert (apply [q 1; q 2; q 3; q 4] (q 2) = q 49)

  (* a + bx + cx^2 + 0x^3 = a  + bx + cx^2 *)
  let normalize p =
    let rp = List.rev p in
    let rec loop = function
      | [] -> []
      | x :: rp when A.(x = zero) -> loop rp
      | rp -> rp
    in
    List.rev (loop rp)

  let rec add p1 p2 =
    match (p1, p2) with
    | [], p2 -> p2
    | p1, [] -> p1
    | a1 :: p1, a2 :: p2 -> A.(a1 + a2) :: add p1 p2

  let add p1 p2 = normalize @@ add p1 p2

  let sum = List.fold_left add zero

  let mul_scalar n p =
    if A.( n = zero ) then [] else List.map A.(fun m -> n * m) p

  let neg = List.map A.( ~- )

  let mul p1 p2 =
    let ps =
      List.mapi
        (fun i a ->
          List.rev_append (List.init i (fun _ -> A.zero)) @@ mul_scalar a p2)
        p1
    in
    sum ps

  (* 1 + x + x^2  *  1 + x + x^2 + x^3
     = 1 + 2x + 3x^2 + 3x^3 + 2x^4 + x^5 *)
  let test_mul () =
    let p = mul [A.one; A.one; A.one] [A.one; A.one; A.one; A.one] in
    Format.ef "test_mul: %a@." pp p ;
    let q = A.of_int in
    assert (p = [q 1; q 2; q 3; q 3; q 2; q 1])

  (* p1 / p2 *)
  let div_rem p1 p2 =
    let p1 = normalize p1 in
    let p2 = normalize p2 in
    assert (p2 <> zero) ;
    let rp1 = List.rev p1 in
    let rp2 = List.rev p2 in
    let rp2hd = List.hd rp2 in
    let rp2tl = List.tl rp2 in
    let rp2len = List.length rp2 in
    let rec loop rp1 =
      if List.length rp1 < rp2len then ([], rp1)
      else
        match rp1 with
        | [] -> assert false
        | a1 :: rp1 ->
            let d = A.(a1 / rp2hd) in
            let rec loop' rp1 rp2tl =
              match (rp1, rp2tl) with
              | rp1, [] -> rp1
              | [], _ -> assert false
              | a1 :: rp1, a2 :: rp2tl -> A.(a1 - (d * a2)) :: loop' rp1 rp2tl
            in
            let rp1 = loop' rp1 rp2tl in
            let ds, rem = loop rp1 in
            (d :: ds, rem)
    in
    let ds, rem = loop rp1 in
    (List.rev ds, normalize @@ List.rev rem)

  let gen sz rng =
    let open Random.State in
    let l = sz rng in
    normalize
    @@ List.init l (fun _ ->
           let x = int rng 201 - 100 in
           let y = int rng 201 - 100 in
           let y = if y = 0 then 1 else y in
           A.(of_int x / of_int y))

  let test_div_rem () =
    let open Format in
    let q = A.of_int in
    let d, r = div_rem [q 1; q 2; q 1] [q 1; q 1] in
    prerr_endline "test_div_rem" ;
    ef "div %a@." pp d ;
    ef "rem %a@." pp r ;
    let d, r = div_rem [q 1; q 1] [q 1; q 2; q 1] in
    prerr_endline "test_div_rem" ;
    ef "div %a@." pp d ;
    ef "rem %a@." pp r ;
    let test rng =
      let a = gen (Gen.int 20) rng in
      let b = gen (Gen.int 20) rng in
      if b <> zero then (
        let d, r = div_rem a b in
        assert (List.length r < List.length b) ;
        if not (add (mul d b) r = a) then (
          prerr_endline "test_div_rem random test fails" ;
          ef "a: %a@." pp a ;
          ef "b: %a@." pp b ;
          ef "d: %a@." pp d ;
          ef "r: %a@." pp r ;
          assert false))
    in
    let rng = Random.State.make_self_init () in
    for _ = 0 to 1000 do
      test rng
    done ;
    ()

  (* Lagrange base polynomials l_j(x) for j = 1 to #xs *)
  let lagrange_basis (xs : f list) : t list =
    let rec f sx = function
      | [] -> []
      | xj :: xs ->
          (List.fold_left mul one
          @@ List.map (fun xi ->
                 let open A in
                 let xj_xi = xj - xi in
                 assert (not (xj_xi = zero)) ;
                 [~-xi / xj_xi; one / xj_xi]
                 (* (x - xi) / (xj - xi) *))
          @@ List.rev_append sx xs)
          :: f (xj :: sx) xs
    in
    f [] xs

  let interpolate (xys : (f * f) list) : t =
    let ls = lagrange_basis @@ List.map fst xys in
    sum @@ List.map2 (fun (_, y) l -> mul_scalar y l) xys ls

  let test_interpolate () =
    let open Format in
    let q = A.of_int in
    let test xys =
      let xys = List.map (fun (x, y) -> (q x, q y)) xys in
      let f = interpolate xys in
      ef "%a@." pp f ;
      List.iter (fun (x, y) -> assert A.(apply f x = y)) xys
    in
    test [(0, 1); (1, 2)] ;
    test [(0, 10); (3, 9)] ;
    test [(1, 3); (2, 2); (3, 4)]

  let test_normalize () =
    assert (normalize [A.zero] = zero)

  let z fs : t =
    let q = A.of_int in
    List.fold_left mul one
    @@ List.map (fun f -> [A.(~-) f; q 1] (* x - f *)) fs

  let degree t =
    let len = List.length (normalize t) in
    if len = 0 then 0 else len - 1

  let is_zero t = normalize t = zero

  let equal t1 t2 =
    let rec loop t1 t2 =
      match t1, t2 with
      | [], [] -> true
      | c1::t1, c2::t2 when A.(c1 = c2) -> loop t1 t2
      (* covers the non normalized cases *)
      | c1::t1, [] when A.(c1 = zero) -> loop t1 []
      | [], c2::t2 when A.(c2 = zero) -> loop t2 []
      | _ -> false
    in
    loop t1 t2

  module Infix = struct
    let (+) = add
    let (-) x y = add x (neg y)
    let (~-) = neg
    let ( * ) = mul
    let ( *$ ) = mul_scalar
    let (/%) = div_rem
  end

  let test () =
    test_apply () ;
    test_mul () ;
    test_interpolate () ;
    test_div_rem () ;
    test_normalize ()
end

let conv f = List.map f

let () =
  let module PQ = Make(Q) in
  PQ.test ()
