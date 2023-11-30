include module type of struct include Stdlib.Format end

type t = Stdlib.Format.formatter

type 'a printer = Stdlib.Format.formatter -> 'a -> unit

val list : (unit, formatter, unit) format -> 'a printer -> 'a list printer

val seq : (unit, formatter, unit) format -> 'a printer -> 'a Seq.t printer

val f : formatter -> ('a, formatter, unit) format -> 'a

val ef : ('a, formatter, unit) format -> 'a

val int : int printer

val string : string printer
