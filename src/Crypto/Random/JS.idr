module Crypto.Random.JS

import Crypto.Random
import System.FFI
import Data.Vect
import Utils.Misc
import Data.Buffer
import System.Info

%foreign "node:lambda:n => require('crypto').randomBytes(n)"
prim_io__randomBytes : Int -> PrimIO Buffer

-- Test this
%foreign "javascript:lambda:n => crypto.getRandomValues(new Uint8Array(n))"
prim_io__getRandomValues : Int -> PrimIO Buffer

buffer_content : HasIO io => (Int -> PrimIO Buffer) -> (n : Nat) -> io (Vect n Bits8)
buffer_content f n = do
  buffer <- primIO $ f (cast n)
  traverse (getBits8 buffer) $ map (cast . finToNat) range

public export
HasIO io => MonadRandom io where
  random_bytes Z = pure []
  random_bytes n =
  case codegen of
    "node" => buffer_content prim_io__randomBytes n
    "javascript" => buffer_content prim_io__getRandomValues n
    _ => assert_total $ idris_crash "no random backend availible"
