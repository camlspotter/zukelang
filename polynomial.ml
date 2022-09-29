let q = Q.of_int

type polynomial = int list (* a + bx + cx^2 + dx^3 *)

let pp_list_sep fmt = fun ppf () -> Format.fprintf ppf fmt

let zero = []
let one = [Q.one]

let pp ppf p =
  let open Format in
  match p with
  | [] -> Q.pp_print ppf Q.zero
  | _ ->
      pp_print_list ~pp_sep:(pp_list_sep " + ") (fun ppf (i,p) ->
          if i = 0 then fprintf ppf "%a" Q.pp_print p
          else if i = 1 then fprintf ppf "%a x" Q.pp_print p
          else fprintf ppf "%a x^%d" Q.pp_print p i)
        ppf @@ List.mapi (fun i a -> (i,a)) p

let apply f x =
  fst @@
  List.fold_left (fun (acc,xi) a ->
      Q.(acc + a * xi, xi * x)) (Q.zero, Q.one) f

let test_apply () =
  (* 1 + 2x + 3x^2 + 4x^3  for x = 2 = 49 *)
  assert (apply [q 1; q 2; q 3; q 4] (q 2) = q 49)

(* a + bx + cx^2 + 0x^3 = a  + bx + cx^2 *)
let normalize p =
  let rp = List.rev p in
  let rec loop = function
    | [] -> []
    | x::rp when Q.equal x Q.zero -> loop rp
    | rp -> rp
  in
  List.rev (loop rp)

let rec add p1 p2 =
  match p1, p2 with
  | [], p2 -> p2
  | p1, [] -> p1
  | a1::p1, a2::p2 -> Q.(a1 + a2)::add p1 p2

let add p1 p2 = normalize @@ add p1 p2

let mul_scalar n p =
  if Q.equal n Q.zero then [] else List.map Q.(fun m -> n * m) p

let neg = List.map Q.(~-)

let mul p1 p2 =
  let ps =
    List.mapi (fun i a ->
        List.rev_append (List.init i (fun _ -> Q.zero)) @@ mul_scalar a p2
      ) p1
  in
  List.fold_left add zero ps

(* 1 + x + x^2  *  1 + x + x^2 + x^3
   = 1 + 2x + 3x^2 + 3x^3 + 2x^4 + x^5 *)
let test_mul () =
  let p = mul [Q.one; Q.one; Q.one]  [Q.one; Q.one; Q.one; Q.one] in
  Format.eprintf "test_mul: %a@." pp p;
  assert (p = [q 1; q 2; q 3; q 3; q 2; q 1])

(* p1 / p2 *)
let div_rem p1 p2 =
  let p1 = normalize p1 in
  let p2 = normalize p2 in
  assert (p2 <> zero);
  let rp1 = List.rev p1 in
  let rp2 = List.rev p2 in
  let rp2hd = List.hd rp2 in
  let rp2tl = List.tl rp2 in
  let rp2len = List.length rp2 in
  let rec loop rp1 =
    if List.length rp1 < rp2len then [], rp1
    else
      match rp1 with
      | [] -> assert false
      | a1::rp1 ->
          let d = Q.(a1 / rp2hd) in
          let rec loop' rp1 rp2tl =
            match rp1, rp2tl with
            | rp1, [] -> rp1
            | [], _ -> assert false
            | a1::rp1, a2::rp2tl ->
                Q.(a1 - d * a2) :: loop' rp1 rp2tl
          in
          let rp1 = loop' rp1 rp2tl in
          let ds, rem = loop rp1 in
          d::ds, rem
  in
  let ds, rem = loop rp1 in
  List.rev ds, normalize @@ List.rev rem

let gen rng =
  let open Random.State in
  let l = int rng 20 in
  normalize @@
  List.init l (fun _ ->
      let x = int rng 201 - 100 in
      let y = int rng 201 - 100 in
      let y = if y = 0 then 1 else y in
      Q.(q x / q y))

let test_div_rem () =
  let d, r = div_rem [q 1; q 2; q 1] [q 1; q 1] in
  prerr_endline "test_div_rem";
  Format.eprintf "div %a@." pp d;
  Format.eprintf "rem %a@." pp r;
  let d, r = div_rem [q 1; q 1] [q 1; q 2; q 1] in
  prerr_endline "test_div_rem";
  Format.eprintf "div %a@." pp d;
  Format.eprintf "rem %a@." pp r;
  let test rng =
    let a = gen rng in
    let b = gen rng in
    if b <> zero then
      let d, r = div_rem a b in
      assert (List.length r < List.length b);
      if not (add (mul d b) r = a) then begin
        prerr_endline "test_div_rem random test fails";
        Format.eprintf "a: %a@." pp a;
        Format.eprintf "b: %a@." pp b;
        Format.eprintf "d: %a@." pp d;
        Format.eprintf "r: %a@." pp r;
        assert false
      end
  in
  let rng = Random.State.make_self_init () in
  for _ = 0 to 1000 do
    test rng
  done;
  ()

(* Lagrange base polynomials l_j(x) for j = 1 to #xs *)
let ls xs =
  let rec f sx = function
    | [] -> []
    | xj::xs ->
        (List.fold_left mul one
         @@ List.map (fun xi ->
             let xj_xi = let open Q in xj - xi in
             assert (Q.compare xj_xi Q.zero <> 0);
             Q.[~- xi / xj_xi ; one / xj_xi ] (* -xi + x *))
         @@ List.rev_append sx xs)
        :: f (xj::sx) xs
  in
  f [] xs

let interporate xys =
  let ls = ls @@ List.map fst xys in
  List.fold_left add zero
  @@ List.map2 (fun (_,y) l -> mul_scalar y l) xys ls

let test_interporate () =
  let test xys =
    let xys = List.map (fun (x,y) -> q x, q y) xys in
    let f = interporate xys in
    Format.eprintf "%a@." pp f;
    List.iter (fun (x,y) -> assert (Q.equal (apply f x) y)) xys
  in
  test [(0,1); (1,2)];
  test [(0,10); (3,9)];
  test [(1,3); (2,2); (3,4)]

let () =
  test_apply ();
  test_mul ();
  test_interporate ();
  test_div_rem ()
