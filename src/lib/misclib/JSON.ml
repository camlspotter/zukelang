type json = Yojson.Safe.t
type t = json

module Conv = struct
  open Ppx_yojson_conv_lib
  include Yojson_conv

  module type S = Yojsonable.S
  module type S1 = Yojsonable.S1
  module type S2 = Yojsonable.S2
  module type S3 = Yojsonable.S3
end
