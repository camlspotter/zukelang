open Misc

module C = struct
  type t = Q.t * Q.t

  let ( + ) (a,b) (c,d) = Q.(a + b, c + d)
  let ( - ) (a,b) (c,d) = Q.(a - b, c - d)
  let ( * ) (a,b) (c,d) = Q.(a * b - c * d, a * d + b * c)
  let ( / ) (a,b) (c,d) =
    (* $(a+bi) / (c+di) = ((a+bi) * (c-di)) / ((c+di) * (c-di))$ *)
    (* $= (ac+bd - adi + bci) / (c^2+d^2)$ *)
    let open Q in
    let c2d2 = c*c + d*d in
    Q.( (a*c + b*d) / c2d2, (b * c - a * d) / c2d2 )

  let test () =
    let c r i = Q.of_int r, Q.of_int i in
    assert (c 2 3 / c 1 (-2) = c (-4) 7 / c 5 0);
    assert (c (-4) 5 / c (-1) 1 = c 9 (-1) / c 2 0);
    assert (c 3 (-4) / c 2 1 = c 2 (-11) / c 5 0)
end

let log2 =
  let l2 = log 2.0 in
  fun f -> log f /. l2

module Polynomial = Polynomial.Make(Q)

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
  let union map1 map2 =
    union (fun _k c1 c2 ->
        let c = Q.(c1 + c2) in
        if Q.(c = zero) then None
        else Some c) map1 map2

  let pp ppf map =
    Format.(seq ",@ " (fun ppf (k, ck) -> f ppf "%d:%a" k Q.pp ck))
      ppf
      @@ to_seq map

end

let slow_dft (f : Polynomial.t) =
  let d = Polynomial.degree f in
  let n (* $N$ *) = 1 lsl (int_of_float @@ ceil @@ log2 (float (d + 1))) in
  let module ZetaMap = ZetaMap(struct let n = n end) in
  (* $\hat{f}(t) = \Sigma_{i=0}^{N-1} f(\zeta^i_N)t^i$
          $= \Sigma_{i=0}^{N-1} \Sigma_{j=0}^{N-1} c_j (\zeta^i_N)^j t^i$
          $= \Sigma_{j=0}^{N-1} c_j \Sigma_{i=0}^{N-1} (\zeta^j_N t)^i$

     $\hat{f}(\zeta_N^{-k}) = \Sigma_{j=0}^{N-1}c_j \Sigma_{i=0}^{N-1}(\zeta_N^j \zeta_N^{-k})^i$
             $= \Sigma_{j=0}^{N-1} c_j \Sigma_{i=0}^{N-1}(\zeta_N^{i(j-k)})$
             $= \Sigma_{j=0}^{N-1} c_j \mathrm{~if~} j=k \mathrm{~then~} N \mathrm{~else~} 0$ since the orthogonality of $\zeta_N$
             $= N c_k$
  *)
  let fzN k (* $f(\zeta_N^k)$ where $f(x) = \Sigma_{j=0}^{N-1} c_j x^j$ *) =
    (* $f(\zeta_N^k) = \Sigma_{j=0}^{N-1} c_j (\zeta_N^k)^j = \Sigma_{j=0}^{N-1} c_j \zeta_N^{jk}$ *)
    Seq.fold_left (fun map (j, cj) -> ZetaMap.add (j * k) cj map)
      ZetaMap.empty @@ Seq.mapi (fun j cj -> (j, cj)) @@ List.to_seq f
  in
  let f'zN k (* $\hat{f}(\zeta_N^k) = \Sigma_{i=0}^{N-1} f(\zeta^i_N)\zeta_N^{ik}$ *) =
    let g i (* $f(\zeta^i_N)\zeta_N^{ik}$ *) =
      let fzNi (* $f(\zeta_N^i)$ *) = fzN i in
      ZetaMap.fold (fun l cl  (* $c_l\zeta_N^l$ *) acc ->
          (* $c_l\zeta_N^l \cdot \zeta_N^{ik}  = c_i \zeta_N^{l+ik}$ *)
          (* TODO: The sums of $\zeta_N^j$ where $j \not \in \{0, N/2\}$
             must be 0 therefore we can skip their additions *)
           ZetaMap.add (l + i * k) cl acc)
        fzNi ZetaMap.empty
    in
    List.fold_left ZetaMap.union ZetaMap.empty (List.init n g)
  in
  let f2 =
    List.init (d + 1) (fun k ->
        let map = f'zN (n-k) in
        ZetaMap.iter (fun i _ -> if i <> 0 then (
            Format.ef "??? %a@." ZetaMap.pp map;
            assert false
          ) ) map;
        Q.(Option.value ~default:zero (ZetaMap.find_opt 0 map) / of_int n))
  in
  if not (Polynomial.equal f f2) then
    Format.ef "??? %a@." Polynomial.pp f2;
  assert (Polynomial.equal f f2)

let test () =
  let (!) n = Q.of_int n in
  slow_dft [];
  slow_dft [!1];
  slow_dft [!9];
  slow_dft [!2];
  slow_dft [!1; !1];
  slow_dft [!9; !4];
  slow_dft [!9; !8; !7; !6; !5; !4; !3];
  slow_dft [!1; !2; !3];
  let rng = Random.State.make_self_init () in
  for _ = 0 to 1000 do
    let p = Polynomial.gen rng in
    slow_dft p
  done
