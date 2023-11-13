open Misc

let log2 =
  let l2 = log 2.0 in
  fun f -> log f /. l2

module PQ = Polynomial.Make(Q)

(* $m = \Sigma_k c_k \zeta_N^k$ *)
module ZetaMap(N : sig val n : int end) = struct
  include Map.Make(Int)

  let () = assert (N.n = 1 || N.n mod 2 = 0)

  let n2 (* n / 2 *) = N.n / 2

  (* $m + c_k \zeta_N^k$ *)
  let add k ck map =
    if Q.(ck = zero) then map
    else
      let k = k mod N.n in
      let k = if k < 0 then k + N.n else k in
      (* $\zeta_N^k = -\zeta_N^{k - N/2}$ *)
      let k, ck = if N.n > 1 && k >= n2 then k - n2, Q.(~- ck) else k, ck in
      update k (fun co ->
          match co with
          | None -> Some ck
          | Some c ->
              let c = Q.(c + ck) in
              if Q.(c = zero) then None else Some c) map

  (* $m_1 + m_2$ *)
  let _union map1 map2 =
    union (fun _k c1 c2 ->
        let c = Q.(c1 + c2) in
        if Q.(c = zero) then None
        else Some c) map1 map2

  let _pp ppf map =
    Format.(seq ",@ " (fun ppf (k, ck) -> f ppf "%d:%a" k Q.pp ck))
      ppf
      @@ to_seq map

end

let dft fzNs (* $f(\zeta_N^k)$ where $f(x) = \Sigma_{j=0}^{N-1} c_j x^j$ *) =
  let n = Array.length fzNs in
  let module ZetaMap = ZetaMap(struct let n = n end) in
  (* $\hat{f}(t) = \Sigma_{i=0}^{N-1} f(\zeta^i_N)t^i$
          $= \Sigma_{i=0}^{N-1} \Sigma_{j=0}^{N-1} c_j (\zeta^i_N)^j t^i$
          $= \Sigma_{j=0}^{N-1} c_j \Sigma_{i=0}^{N-1} (\zeta^j_N t)^i$

     $\hat{f}(\zeta_N^{-k}) = \Sigma_{j=0}^{N-1}c_j \Sigma_{i=0}^{N-1}(\zeta_N^j \zeta_N^{-k})^i$
             $= \Sigma_{j=0}^{N-1} c_j \Sigma_{i=0}^{N-1}(\zeta_N^{i(j-k)})$
             $= \Sigma_{j=0}^{N-1} c_j \mathrm{~if~} j=k \mathrm{~then~} N \mathrm{~else~} 0$ since the orthogonality of $\zeta_N$
             $= N c_k$
  *)
  let f'zN k (* $\hat{f}(\zeta_N^k) = \Sigma_{i=0}^{N-1} f(\zeta^i_N)\zeta_N^{ik}$ *) =
    let g i (* $f(\zeta^i_N)\zeta_N^{ik}$ *) =
      let fzNi (* $f(\zeta_N^i)$ *) = Array.unsafe_get fzNs i in
      ZetaMap.fold (fun l cl  (* $c_l\zeta_N^l$ *) acc ->
          (* $c_l\zeta_N^l \cdot \zeta_N^{ik}  = c_i \zeta_N^{l+ik}$ *)
          let lik = l + i * k in
          (* The sums of $\zeta_N^j$ where $j \not \in \{0, N/2\}$ must be 0
             therefore we can skip their additions *)
          match lik mod n with
          | 0 -> Q.(acc + cl)
          | x when x * 2 = n -> Q.(acc - cl)
          | _ -> acc)
        fzNi Q.zero
    in
    List.fold_left Q.(+) Q.zero (List.init n g)
  in
  List.init n (fun k -> Q.(f'zN Stdlib.(n-k) / of_int n))

let test_dft (f : PQ.t) =
  let d = PQ.degree f in
  let n (* $N$ *) = 1 lsl (int_of_float @@ ceil @@ log2 (float (d + 1))) in
  let module ZetaMap = ZetaMap(struct let n = n end) in
  let fzN k (* $f(\zeta_N^k)$ where $f(x) = \Sigma_{j=0}^{N-1} c_j x^j$ *) =
    (* $f(\zeta_N^k) = \Sigma_{j=0}^{N-1} c_j (\zeta_N^k)^j = \Sigma_{j=0}^{N-1} c_j \zeta_N^{jk}$ *)
    Seq.fold_left (fun map (j, cj) -> ZetaMap.add (j * k) cj map)
      ZetaMap.empty @@ Seq.mapi (fun j cj -> (j, cj)) @@ List.to_seq f
  in
  let fzNs = Array.init n fzN in
  let f2 = dft fzNs in
  if not (PQ.equal f f2) then Format.ef "??? %a@." PQ.pp f2;
  assert (PQ.equal f f2)

module Make( F : Field.S ) = struct
  module Polynomial = Polynomial.Make(F)

  module W(N : sig val n : int end) = struct
    open N
    include Map.Make(Int)
    let scale s m =
      if F.(s = zero) then empty
      else map (fun ck -> F.(ck * s)) m
    let add m1 m2 =
      union (fun _k ck1 ck2 ->
          let ck = F.(ck1 + ck2) in
          if F.(ck = zero) then None else Some ck) m1 m2
    let rot k m (* $\zeta_N^k * m$ *) =
      fold (fun i ck acc ->
          if F.(ck = zero) then acc
          else
            let k = (k + i) mod n in
            let k = if k < 0 then k + n else k in
            let k, ck =
              if n > 1 && k >= n / 2 then k - n / 2, F.(~-) ck
              else k, ck
            in
            update k (function
                | None -> Some ck
                | Some c ->
                    let c = F.(c + ck) in
                    if F.(c = zero) then None else Some c) acc)
        m empty

    let _pp ppf m =
      Format.(seq ",@ " (fun ppf (k, ck) -> f ppf "%d:%a" k F.pp ck)) ppf
      @@ to_seq m
  end

  (* https://faculty.sites.iastate.edu/jia/files/inline-files/polymultiply.pdf *)
  let gen_fft ~inv a (* length must be $n = 2^m$ *) =
    let n = Array.length a in
    let module W = W(struct let n = n end) in
    let n0 = n in
    let n02 = n0 / 2 in
    let rec loop a =
      let n = Array.length a in
      if n <= 1 then a
      else
        let (#!) = Array.unsafe_get in
        let a0 = Array.init (n/2) (fun i -> a #! (i*2)) in
        let a1 = Array.init (n/2) (fun i -> a #! (i*2+1)) in
        let a'0 = loop a0 in
        let a'1 = loop a1 in
        let n2 = n / 2 in
        Array.init n (fun k ->
            if k < n2 then
              let k' = if inv then -k else k in
              W.add (a'0 #! k) (W.rot (k' * n0 / n) (a'1 #! k))
            else
              let k = k - n2 in
              let k' = if inv then -k else k in
              W.add (a'0 #! k) (W.rot (k' * n0 / n + n02) (a'1 #! k)))
    in
    if inv then
      Array.map (W.scale F.(one / of_int n)) @@ loop a
    else loop a

  let fft f =
    let d = Polynomial.degree f in
    let n (* $N$ *) = 1 lsl (int_of_float @@ ceil @@ log2 (float (d + 1))) in
    let module W = W(struct let n = n end) in
    let a = Array.(append (of_list f) (init (n - d - 1) (fun _ -> F.zero))) in
    let a = Array.map (fun c -> W.singleton 0 c) a in
    gen_fft ~inv:false a

  let ifft vs =
    let module W = W(struct let n = Array.length vs end) in
    let a_ = gen_fft ~inv:true vs in
    let f =
      Array.to_list @@ Array.map (fun m ->
          (* W.iter (fun k _ -> if k <> 0 then assert false) m; *)
          Option.value ~default:F.zero @@ W.find_opt 0 m) a_
    in
    Polynomial.normalize f

  let test_fft f =
    let a' = fft f in
    let f' = ifft a' in
    assert (Polynomial.equal f f')
end

let test () =
  let (!) n = Q.of_int n in
  test_dft [];
  test_dft [!1];
  test_dft [!9];
  test_dft [!2];
  test_dft [!1; !1];
  test_dft [!9; !4];
  test_dft [!9; !8; !7; !6; !5; !4; !3];
  test_dft [!1; !2; !3];
  let rng = Random.State.make_self_init () in
  for _ = 0 to 1000 do
    let p = PQ.gen rng in
    test_dft p
  done;
  prerr_endline "FFT";
  let module FFT = Make(Q) in
  let open FFT in
  test_fft [];
  test_fft [!3];
  test_fft [!3; !2];
  test_fft [!1; !9];
  test_fft [!3; !2; !4];
  test_fft [!9; !8; !7; !6; !5; !4; !3];
  let rng = Random.State.make_self_init () in
  for _ = 0 to 1000 do
    let p = Polynomial.gen rng in
    test_fft p
  done;
