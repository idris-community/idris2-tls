module Crypto.Random.C

import Crypto.Random
import System.FFI
import Data.Vect
import Utils.Misc
import Data.Buffer
import Data.List
import System.Info

%foreign "C:random_buf,libidristls"
prim_io__random_buf : Buffer -> Int -> PrimIO Int

public export
HasIO io => MonadRandom io where
  random_bytes Z = pure []
  random_bytes n = do
    let n' = cast n
    Just buf <- newBuffer n'
    | Nothing => assert_total $ idris_crash "somehow newBuffer failed"
    0 <- primIO $ prim_io__random_buf buf n'
    | _ => assert_total $ idris_crash "random_buf failed"
    traverse (getBits8 buf) (map (cast . finToNat) Fin.range)
