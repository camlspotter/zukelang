include module type of struct include Stdlib.Option end

include Monad.T with type 'a t = 'a option
