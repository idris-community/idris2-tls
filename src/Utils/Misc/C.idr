module Utils.Misc.C

import Data.Vect
import Network.FFI
import System.FFI

public export
peek_byte : HasIO m => AnyPtr -> (offset : Int) -> m Bits8
peek_byte ptr offset = do
  ret <- primIO $ prim__idrnet_peek ptr offset
  pure $ cast ret

public export
peek_bytes : HasIO m => AnyPtr -> (offset : Int) -> (n : Nat) -> m (Vect n Bits8)
peek_bytes ptr offset Z = pure []
peek_bytes ptr offset (S n) = do
  ret <- peek_byte ptr offset
  rets <- peek_bytes ptr (offset + 1) n
  pure $ ret :: rets

export
poke_byte : HasIO m => AnyPtr -> (offset : Int) -> Bits8 -> m ()
poke_byte ptr offset b = do
  primIO $ prim__idrnet_poke ptr offset (cast b)

export
poke_bytes : HasIO m => AnyPtr -> (offset : Int) -> List Bits8 -> m ()
poke_bytes ptr offset [] = pure ()
poke_bytes ptr offset (x :: xs) = do
  poke_byte ptr offset x
  poke_bytes ptr (offset + 1) xs

export
with_bytes : HasIO m => List Bits8 -> (AnyPtr -> m a) -> m a
with_bytes bytes f = do
  let nbytes = cast {to = Int} $ length bytes
  ptr <- malloc nbytes
  poke_bytes ptr 0 bytes
  f ptr
