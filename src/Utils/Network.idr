module Utils.Network

import Data.Vect
import Network.FFI
import Network.Socket
import Network.Socket.Raw
import System.FFI
import Utils.Misc.C

export
%foreign "C:send,libc"
prim__socket_send : SocketDescriptor -> (ptr : AnyPtr) -> (nbytes : Int) -> (flags : Bits32) -> PrimIO Int32

export
%foreign "C:recv,libc"
prim__socket_recv : SocketDescriptor -> (ptr : AnyPtr) -> (nbytes : Int) -> (flags : Bits32) -> PrimIO Int32

||| Linux: when send() returns == -1, errno is set; returns >= 0, number of bytes sent
export
send_bytes : HasIO m => Socket -> List Bits8 -> m (Maybe Int)
send_bytes sock bytes = do
  with_bytes bytes $ \ptr => do
    ret <- primIO $ prim__socket_send sock.descriptor ptr (cast $ length bytes) 0
    case ret < 0 of -- ret == -1
      True => pure Nothing
      False => pure $ Just $ cast ret

||| Linux: when recv() returns == -1, errno is set
export
recv_bytes : HasIO m => Socket -> (max_size : Int) -> m (Maybe (List Bits8))
recv_bytes sock max_size = do
  ptr <- malloc max_size
  ret <- primIO $ prim__socket_recv sock.descriptor ptr max_size 0
  case ret < 0 of -- ret == -1
    True => do
      free ptr
      pure Nothing
    False => do
      bytes <- peek_bytes ptr 0 (cast {to = Nat} ret)
      free ptr
      pure $ Just $ toList bytes
