type 'a comparator = 'a -> 'a -> int

val with_time : (unit -> 'a) -> 'a * float

val log2 : float -> float

val failwithf : ('a, Format.formatter, unit, 'b) format4 -> 'a

val invalid_argf : ('a, Format.formatter, unit, 'b) format4 -> 'a

module Converter : sig
  module type S = sig
    type src
    type dst
    val encode : src -> dst
    val decode : dst -> src Error.result
  end
end

module Z : sig
  include module type of struct include Z end

  val of_z : Z.t -> t

  val gen : t -> t Gen.t

  val pp : t Format.printer

  val yojson_of_t : t -> JSON.t

  val t_of_yojson : JSON.t -> t
end

module Q : sig
  include module type of struct include Q end

  val pp : t Format.printer

  val t_of_yojson : JSON.t -> t

  val yojson_of_t : t -> JSON.t

  val is_zero : t -> bool

  val of_z : Z.t -> t
end
