open Utils

type 'a t = {a : 'a; b : 'a; c : 'a}

val pp : 'a printer -> 'a t printer
