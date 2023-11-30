type json = Yojson.Safe.t

type t = json

module Conv : sig
  include module type of struct
    include Ppx_yojson_conv_lib.Yojson_conv
  end

  module type S = Ppx_yojson_conv_lib.Yojsonable.S
  module type S1 = Ppx_yojson_conv_lib.Yojsonable.S1
  module type S2 = Ppx_yojson_conv_lib.Yojsonable.S2
  module type S3 = Ppx_yojson_conv_lib.Yojsonable.S3
end
