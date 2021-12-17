module Utils.Handle.C

import Utils.Handle
import Utils.Network.C
import Network.Socket
import Data.Nat
import Data.Vect
import Control.Monad.Error.Either

public export
socket_to_handle : HasIO m => Socket -> Handle m
socket_to_handle sock = MkHandle recv send
  where
    recv : (n : Nat) -> EitherT String m (k ** (LTE k n, Vect k Bits8))
    recv size = do
      Just response <- recv_bytes sock $ cast size
      | Nothing => throwE "recv_bytes failed"
      let response' = fromList response
      case isLTE (length response) size of
        Yes prf => pure ((length response) ** (prf, response'))
        No _ => throwE "somehow recv_bytes read more than we ask for"
    send : List Bits8 -> EitherT String m ()
    send body = do
      Just _ <- send_bytes sock body
      | Nothing => throwE "send_bytes failed"
      pure ()
