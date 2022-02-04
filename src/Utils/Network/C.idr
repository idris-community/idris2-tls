module Utils.Network.C

import Data.Vect
import Data.List
import Network.FFI
import Network.Socket
import Network.Socket.Raw
import System.FFI
import Data.Buffer

export
%foreign "C:sock_send,libidristls"
prim__socket_send : SocketDescriptor -> (content : Buffer) -> (nbytes : Int) -> (flags : Bits32) -> PrimIO Int32

export
%foreign "C:sock_recv,libidristls"
prim__socket_recv : SocketDescriptor -> (content : Buffer) -> (nbytes : Int) -> (flags : Bits32) -> PrimIO Int32

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
  let len' = cast $ length bytes
  Just buffer <- newBuffer len'
  | Nothing => assert_total $ idris_crash "somehow newBuffer failed"
  traverse_ (uncurry (setBits8 buffer)) (zip [0..len'] bytes)
  ret <- primIO $ prim__socket_send sock.descriptor buffer len' 0
  case ret < 0 of
    True => pure $ Left ret
    False => pure $ Right ret

-- Linux: when recv() returns == -1, errno is set
export
recv_bytes : HasIO m => Socket -> (max_size : Int) -> m (Either ErrorCode (List Bits8))
recv_bytes sock max_size = do
  Just buffer <- newBuffer max_size
  | Nothing => pure $ Left (-1)
  ret <- primIO $ prim__socket_recv sock.descriptor buffer max_size 0
  case ret > 0 of
    False => do
      pure $ Left ret
    True => do
      bytes <- traverse (getBits8 buffer) [0..((cast ret)-1)]
      pure $ Right $ toList bytes
