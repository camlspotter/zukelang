open Misclib

(* $\zeta_N^k = -\zeta_N^{k - N/2}$

   $\hat{f}(\zeta_N^{-k}) = \Sigma_{j=0}^{N-1}c_j \Sigma_{i=0}^{N-1}(\zeta_N^j \zeta_N^{-k})^i$
           $= \Sigma_{j=0}^{N-1} c_j \Sigma_{i=0}^{N-1}(\zeta_N^{i(j-k)})$
           $= \Sigma_{j=0}^{N-1} c_j \mathrm{~if~} j=k \mathrm{~then~} N \mathrm{~else~} 0$ since the orthogonality of $\zeta_N$
           $= N c_k$
*)

module Make(F : sig
    include Field.S

    val zeta : int -> int -> t
    (* [zeta n i] = $\zeta_{N}^i$ where

       $\zeta_N^i =  \zeta_N^j$ when $i = j \mathrm{~mod~} N$

       $\Sigma_{i=0}^{N-1} \zeta_N^{ij} = N$ when $j = 0$
       $\Sigma_{i=0}^{N-1} \zeta_N^{ij} = 0$ when $j \neq 0$
    *)

    val polynomial_equal : t Polynomial.t -> t Polynomial.t -> bool
  end) = struct

  module Polynomial = Polynomial.Make(F)

  (* https://faculty.sites.iastate.edu/jia/files/inline-files/polymultiply.pdf *)
  let gen_fft ~inv a (* length must be $n = 2^m$ *) =
    let (#!) = Array.get in
    let n = Array.length a in
    let zeta_n = F.zeta n in
    let zeta_n =
      (* memoized zeta_n *)
      let memo = Hashtbl.create 101 in
      fun i ->
        match Hashtbl.find memo i with
        | zni -> zni
        | exception Not_found ->
            let zni = zeta_n i in
            Hashtbl.add memo i zni;
            zni
    in
    let rec loop m a =
      (* m * Array.length a = n *)
      let n' = Array.length a in
      if n' <= 1 then a
      else
        let zeta_n' i = zeta_n (i * m) in
        let n'2 = n' / 2 in
        let a0 = Array.init n'2 (fun i -> a #! (i*2)) in
        let a1 = Array.init n'2 (fun i -> a #! (i*2+1)) in
        let a'0 = loop (m * 2) a0 in
        let a'1 = loop (m * 2) a1 in
        Array.init n' (fun k ->
            if k < n'2 then
              let k' = if inv then -k else k in
              F.(a'0#!k + zeta_n' k' * a'1#!k)
            else
              let k = k - n'2 in
              let k' = if inv then -k else k in
              F.(a'0#!k + zeta_n' Stdlib.(k' + n'2) * a'1#!k))
    in
    if inv then
      (* TODO: we may use mutation *)
      Array.map (fun x -> F.(x / of_int n))  @@ loop 1 a
    else loop 1 a

  let fft ?degree f =
    let d = Polynomial.degree f in
    let n (* $N$ *) =
      let d =
        match degree, d with
        | None, d -> d
        | Some d', d -> max d' d
      in
      1 lsl (int_of_float @@ ceil @@ log2 (float (d + 1)))
    in
    let f = Array.of_list f in
    let a = Array.(append f (init (n - Array.length f) (fun _ -> F.zero))) in
    gen_fft ~inv:false a

  let ifft vs =
    let a_ = gen_fft ~inv:true vs in
    let f = Array.to_list a_ in
    Polynomial.normalize f

  let test_fft f =
    let a' = fft f in
    let f' = ifft a' in
    if not (F.polynomial_equal f f') then begin
      Format.ef "test_fft failed:@.";
      Format.ef "  %a@." Polynomial.pp f;
      Format.ef "  %a@." Polynomial.pp f';
      assert false
    end

  let polynomial_mul p1 p2 =
    let d1 = Polynomial.degree p1 in
    let d2 = Polynomial.degree p2 in
    let degree = d1 + d2 in
    let a1 = fft ~degree p1 in
    let a2 = fft ~degree p2 in
    let a = Array.map2 F.( * ) a1 a2 in
    ifft a

  let test_polynomial_mul p1 p2 =
    assert (F.polynomial_equal (polynomial_mul p1 p2) (Polynomial.mul p1 p2))
end

module FFT_C = Make(struct
    include C

    let equal (r1,i1) (r2,i2) =
      Float.abs (r1 -. r2) <= 0.0001
      && Float.abs (i1 -. i2) <= 0.0001

    let polynomial_equal f f' =
      let rec loop t1 t2 =
        match t1, t2 with
        | [], [] -> true
        | c1::t1, c2::t2 when equal c1 c2 -> loop t1 t2
        (* covers the non normalized cases *)
        | c1::t1, [] when equal c1 C.zero -> loop t1 []
        | [], c2::t2 when equal c2 C.zero -> loop t2 []
        | _ -> false
      in
      loop f f'
  end)

let test_c () =
  prerr_endline "FFT_C";
  let open FFT_C in
  let (!) = C.of_int in
  test_fft [];
  test_fft [!3];
  test_fft [!3; !2];
  test_fft [!1; !9];
  test_fft [!3; !2; !4];
  test_fft [!9; !8; !7; !6; !5; !4; !3];
  let rng = Gen.init_auto () in
  for _ = 0 to 1000 do
    let p = Polynomial.gen (Gen.int 20) rng in
    test_fft p
  done;
  test_polynomial_mul [!1; !2] [!3; !4];
  test_polynomial_mul [] [!3; !4];
  for _ = 0 to 10000 do
    let p1 = Polynomial.gen (Gen.int 20) rng in
    let p2 = Polynomial.gen (Gen.int 20) rng in
    test_polynomial_mul p1 p2
  done;
  let benchmark n =
    let samples =
      List.init 10 (fun _ ->
          let p1 = Polynomial.gen (Gen.return n) rng in
          let p2 = Polynomial.gen (Gen.return n) rng in
          p1, p2)
    in
    let (), t_fft =
      with_time (fun () ->
          List.iter (fun (p1,p2) -> ignore @@ polynomial_mul p1 p2) samples)
    in
    let (), t_naive =
      with_time (fun () ->
          List.iter (fun (p1,p2) -> ignore @@ Polynomial.mul p1 p2) samples)
    in
    Format.ef "n: %d FFT: %f  Naive: %f  ratio: %f@." n t_fft t_naive (t_fft /. t_naive)
  in
  benchmark 10;
  benchmark 20;
  benchmark 30;
  benchmark 40;
  benchmark 50; (* x0.8 FFT is faster than the naive algorithm from here. *)
  benchmark 100; (* x0.3 *)
  benchmark 1000; (* x0.03 *)
  prerr_endline "FFT_C end"

module Bls12_381_zeta = struct
  (* #Fr = 2^32 * a + 1 for some odd number a

     From Fermat's little theorem,

       g^(#Fr-1) = 1  (mod #Fr)  for   g \in Fr

       g^(2^32 * a) = 1

       (g^a)^(2^32) = 1
  *)
  open Curve.Bls12_381

  let m, a =
    let module Fr = Curve.Bls12_381.Fr in
    let order = Fr.order in
    let rec f acc i =
      match Z.(div_rem i (of_int 2)) with
      | d, r when Z.(r = zero) -> f (acc + 1) d
      | _ -> acc, i
    in
    let m, a = f 0 Z.(order - one) in
    Format.ef "#Fr = 2^%d * %a + 1@." m Z.pp a;
    m, a

  let () = assert (Fr.order = Z.((one lsl m) * a + one))

  (* pick $g \in Fr$ s.t. $(g^a)^{2^m} \equiv 1$ but $(g^a)^{2^{m-1}} \not \equiv 1$ *)

  let g = 5

  let test g =
    let m_1 = m - 1 in
    let w = Fr.(of_int g ** a) in
    Fr.(w ** Z.(of_int 2 ** m_1) <> one)
    && Fr.(w ** Z.(of_int 2 ** m) = one)

  let () = assert (test g)

  (* a 2^32th primitive root of unity *)
  let w (* $\omega$, $\omega^{2^{32}} \equiv 1$ and $\omega^{2^{31}} \not \equiv 1$ *) = Fr.(of_int g ** a)
end

module FFT_Fr = Make(struct
    include Curve.Bls12_381.Fr

    let polynomial_equal = Poly.equal

    let max_n = 1 lsl 32

    let zeta n =
      if n > max_n then invalid_arg "Fr.zeta";
      if max_n mod n <> 0 then invalid_arg "Fr.zeta";
      fun i -> Bls12_381_zeta.w ** (Z.of_int Stdlib.( max_n / n * i ))
  end)

let test_fr () =
  prerr_endline "FFT_Fr";
  let open FFT_Fr in
  let (!) = Bls12_381.Fr.of_int in
  test_fft [];
  test_fft [!3];
  test_fft [!3; !2];
  test_fft [!1; !9];
  test_fft [!3; !2; !4];
  test_fft [!9; !8; !7; !6; !5; !4; !3];
  let rng = Gen.init_auto () in
  for _ = 0 to 1000 do
    let p = Polynomial.gen (Gen.int 20) rng in
    test_fft p
  done;
  test_polynomial_mul [!1; !2] [!3; !4];
  test_polynomial_mul [] [!3; !4];
  for _ = 0 to 10000 do
    let p1 = Polynomial.gen (Gen.int 20) rng in
    let p2 = Polynomial.gen (Gen.int 20) rng in
    test_polynomial_mul p1 p2
  done;
  let benchmark n =
    let samples =
      List.init 100 (fun _ ->
          let p1 = Polynomial.gen (Gen.return n) rng in
          let p2 = Polynomial.gen (Gen.return n) rng in
          p1, p2)
    in
    let (), t_fft =
      with_time (fun () ->
          List.iter (fun (p1,p2) -> ignore @@ polynomial_mul p1 p2) samples)
    in
    let (), t_naive =
      with_time (fun () ->
          List.iter (fun (p1,p2) -> ignore @@ Polynomial.mul p1 p2) samples)
    in
    Format.ef "n: %d FFT: %f  Naive: %f  ratio: %f@." n t_fft t_naive (t_fft /. t_naive)
  in
  benchmark 10;
  benchmark 20;
  benchmark 30;
  benchmark 40;
  benchmark 50;
  benchmark 100; (* x1.9 *)
  benchmark 200; (* x0.95 *)
  benchmark 1000; (* x0.14 *)
  prerr_endline "FFT_Fr end"

let test () =
  test_c ();
  test_fr ()
