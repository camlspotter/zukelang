module Make(F : sig
    include Field.S

    val zeta : int -> int -> t
    (** [zeta n i] = $\zeta_{N}^i$ where

        $\zeta_N^i =  \zeta_N^j$ when $i = j \mathrm{~mod~} N$

        $\Sigma_{i=0}^{N-1} \zeta_N^{ij} = N$ when $j = 0$
        $\Sigma_{i=0}^{N-1} \zeta_N^{ij} = 0$ when $j \neq 0$
    *)

    val polynomial_equal : t Polynomial.t -> t Polynomial.t -> bool
  end) : sig

  val gen_fft : inv:bool -> F.t array -> F.t array

  val fft : ?degree:int -> F.t Polynomial.t -> F.t array

  val ifft : F.t array -> F.t Polynomial.t

  val polynomial_mul : F.t Polynomial.t -> F.t Polynomial.t -> F.t Polynomial.t
end

module FFT_C : sig

  module Polynomial : module type of Polynomial.Make(C)

  val fft : ?degree:int -> Polynomial.t -> C.t array

  val ifft : C.t array -> Polynomial.t

end

val test : unit -> unit
