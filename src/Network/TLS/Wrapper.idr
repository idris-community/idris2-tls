module Network.TLS.Wrapper

import Data.Nat
import Utils.Misc
import Data.Vect
import Data.List
import Network.TLS.Magic

public export
record Wrapper (mac_size : Nat) where
  constructor MkWrapper
  encrypted_data : List Bits8
  auth_tag : Vect mac_size Bits8

public export
to_application_data : Wrapper mac_size -> List Bits8
to_application_data x = x.encrypted_data <+> toList x.auth_tag

public export
from_application_data : {mac_size : _} -> (application_data : List Bits8) -> Maybe (Wrapper mac_size)
from_application_data xs =
  let xs' = fromList xs in
  case isLTE mac_size (length xs) of
    Yes prf =>
      let
        (encrypted_data, auth_tag) = splitAt (minus (length xs) mac_size) $ replace_vect (sym $ plusMinusLte _ _ prf) xs'
      in
        Just $ MkWrapper (toList encrypted_data) auth_tag
    No contra => Nothing

public export
record Wrapper2 (mac_size : Nat) where
  constructor MkWrapper2
  iv_data : List Bits8
  encrypted_data : List Bits8
  auth_tag : Vect mac_size Bits8

public export
to_application_data2 : Wrapper2 mac_size -> List Bits8
to_application_data2 x = x.iv_data <+> x.encrypted_data <+> toList x.auth_tag

public export
from_application_data2 : {mac_size : _} -> (iv_size : Nat) -> (application_data : List Bits8) -> Maybe (Wrapper2 mac_size)
from_application_data2 iv_size xs = do
  let (iv, ciphertext) = splitAt iv_size xs
  w <- from_application_data ciphertext
  pure $ MkWrapper2 (toList iv) w.encrypted_data w.auth_tag

namespace WrappedRecord
  public export
  record WrappedRecord where
    constructor MkWrappedRecord
    record_type : RecordType
    wrapped_data : List Bits8

  public export
  to_application_data : WrappedRecord -> List Bits8
  to_application_data x = x.wrapped_data <+> [record_type_to_id x.record_type]
