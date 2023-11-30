include Stdlib.Option

include Monad.Make(struct
    type 'a t = 'a option = None | Some of 'a
    let bind = bind
    let map = map
    let return x = Some x
  end)
