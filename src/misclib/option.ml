include Stdlib.Option

include Monad.Make(struct
    include Stdlib.Option
    let return x = Some x
  end)
