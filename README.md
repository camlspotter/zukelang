# 瑞慶覧(Zukelang), OCaml implemetation of ZK algorithms

![](docs/green-shisa-25.png)

## `src/pinocchio/`

Protocol 2 of [Pinochio: Nearly Practical Verifiable Computation](https://eprint.iacr.org/2013/279.pdf) 

Test program: `dune exec src/pinocchio/test/main.exe`

## `src/groth16/`

Algorithm described in the section 3 of 
[On the Size of Pairing-based Non-interactive Arguments](https://eprint.iacr.org/2016/260.pdf),
with some help of [The zero knowledge blog](https://www.zeroknowledgeblog.com/index.php/groth16).

Test program: `dune exec src/groth16/test/main.exe`

## `Math.Lang`

`Math.Lang.Make(F).Expr.C` provides a minimal DSL to write ZK programs:

- `input name security ty` introduces an input named `name` of `security` and `ty`.
- `let_ a @@ fun x -> body` is for a let binding `let x = a in body`
- Binary product and sum types are available:
  - Product
    - constructor: `pair`
    - deconstructors: `fst` and `snd`
  - Sum
    - constructors: `left a ty_b` and `right ty_a b`
	- deconstructor: `case a_or_b (fun a -> case_a) (fun b -> case_b)`
