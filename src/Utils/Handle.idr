module Utils.Handle

import Data.Vect
import Data.Nat
import Control.Monad.Error.Either

public export
record Handle (m : Type -> Type) where
  constructor MkHandle
  read : (n : Nat) -> EitherT String m (k ** (LTE k n, Vect k Bits8))
  write : List Bits8 -> EitherT String m ()
