module Utils.Network.C

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

public export
ErrorCode : Type
ErrorCode = Int32

public export
NumBytesSent : Type
NumBytesSent = Int32

-- Linux: when send() returns == -1, errno is set; returns >= 0, number of bytes sent
export
send_bytes : HasIO m => Socket -> List Bits8 -> m (Either ErrorCode NumBytesSent)
send_bytes sock bytes = do
  with_bytes bytes $ \ptr => do
    ret <- primIO $ prim__socket_send sock.descriptor ptr (cast $ length bytes) 0
    case ret < 0 of
      True => pure $ Left ret
      False => pure $ Right ret

-- Linux: when recv() returns == -1, errno is set
export
recv_bytes : HasIO m => Socket -> (max_size : Int) -> m (Either ErrorCode (List Bits8))
recv_bytes sock max_size = do
  ptr <- malloc max_size
  ret <- primIO $ prim__socket_recv sock.descriptor ptr max_size 0
  case ret > 0 of
    False => do
      free ptr
      pure $ Left ret
    True => do
      bytes <- peek_bytes ptr 0 (cast {to = Nat} ret)
      free ptr
      pure $ Right $ toList bytes
