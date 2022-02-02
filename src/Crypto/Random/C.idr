module Crypto.Random.C

import Crypto.Random
import System.FFI
import Data.Vect
import Utils.Misc
import Utils.Misc.C
import Data.Buffer
import Data.List
import System.Info

%foreign "C:random_buf,libidrisrandom"
prim_io__random_buf : AnyPtr -> Int -> PrimIO Int

public export
HasIO io => MonadRandom io where
  random_bytes Z = pure []
  random_bytes n = do
    let n' = cast n
    pointer <- malloc n'
    0 <- primIO $ prim_io__random_buf pointer n'
    | _ => free pointer *> (assert_total $ idris_crash "random_buf failed")
    r <- peek_bytes pointer 0 n
    free pointer
    pure r
