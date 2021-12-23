module Utils.Handle.C

import Control.Linear.LIO
import Control.Monad.Error.Either
import Data.Nat
import Data.Vect
import Network.Socket
import Utils.Handle
import Utils.Network.C

||| Turning a non-linear socket from Network.Socket into a Handle tailored for Network.TLS.Handle
export
socket_to_handle : Socket -> Handle Socket () (Res String (const ())) (Res String (const ()))
socket_to_handle sock = MkHandle
  sock
  (\(MkSocket _ _ _ _), wanted => do
    Just output <- recv_bytes sock (cast wanted)
    | Nothing => pure1 $ False # ("recv_bytes failed" # ())
    pure1 $ True # (output # sock)
  )
  (\(MkSocket _ _ _ _), input => do
    Just _ <- send_bytes sock input
    | Nothing => pure1 $ False # ("send_bytes failed" # ())
    pure1 $ True # sock
  )
  (\(MkSocket _ _ _ _) => do
    Socket.close sock
    pure1 ()
  )
