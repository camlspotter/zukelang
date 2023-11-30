include Stdlib.Result

include Monad.Make2(struct
    include Stdlib.Result
    let return x = Ok x
  end)
