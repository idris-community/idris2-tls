module Utils.Handle.C

import Control.Linear.LIO
import Control.Monad.Error.Either
import Data.Nat
import Data.Vect
import Network.Socket
import Utils.Handle
import Utils.Network.C

-- Needed for some reason, sometimes the socket does not read enough bytes
recv_n_bytes : HasIO m => Socket -> Nat -> List Bits8 -> m (Either ErrorCode (List Bits8))
recv_n_bytes sock Z buf = pure (Right [])
recv_n_bytes sock size buf = do
  Right response <- recv_bytes sock $ cast $ minus size $ length buf
  | error => pure error
  let buf = buf <+> response
  if (length buf) >= size 
    then pure $ Right buf
    else recv_n_bytes sock size buf

||| Turning a non-linear socket from Network.Socket into a Handle tailored for Network.TLS.Handle
export
socket_to_handle : Socket -> Handle Socket () (Res String (const ())) (Res String (const ()))
socket_to_handle sock = MkHandle
  sock
  (\(MkSocket _ _ _ _), wanted => do
    Right output <- recv_n_bytes sock wanted []
    | Left code => pure1 $ False # ("recv_bytes failed with code " <+> show code # ())
    pure1 $ True # (output # sock)
  )
  (\(MkSocket _ _ _ _), input => do
    Right _ <- send_bytes sock input
    | Left code => pure1 $ False # ("send_bytes failed with code " <+> show code # ())
    pure1 $ True # sock
  )
  (\(MkSocket _ _ _ _) => do
    Socket.close sock
    pure1 ()
  )
