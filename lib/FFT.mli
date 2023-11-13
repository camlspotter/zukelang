module Make(F : Field.S) : sig

  val fft : Polynomial.Make(F).t -> F.t Map.Make(Int).t array

  val ifft : F.t Map.Make(Int).t array -> Polynomial.Make(F).t

end

val test : unit -> unit
