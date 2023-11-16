module FFT_C : sig

  val fft : ?degree:int -> Polynomial.Make(C).t -> C.t array

  val ifft : C.t array -> Polynomial.Make(C).t

end

val test : unit -> unit
