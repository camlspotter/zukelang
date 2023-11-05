# OCaml implemetation of ZK algorithms

## `pinocchio/`

Protocol 2 of [Pinochio: Nearly Practical Verifiable Computation](https://eprint.iacr.org/2013/279.pdf) 

- No optimization such as polynomial multiplication using fast DFT

```
% dune exec pinocchio/main.exe
```

## `groth16/`

Algorithm described in the section 3 of 
[On the Size of Pairing-based Non-interactive Arguments](https://eprint.iacr.org/2016/260.pdf),
with some help of [The zero knowledge blog](https://www.zeroknowledgeblog.com/index.php/groth16).

```
% dune exec groth16/main.exe
```
