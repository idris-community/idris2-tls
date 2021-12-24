module Crypto.Random

import Control.Monad.Error.Either
import Control.Monad.State
import Crypto.ChaCha
import Data.Bits
import Data.Fin
import Data.List
import Data.Nat
import Data.Stream
import Data.Vect
import Utils.Bytes
import Utils.Misc

public export
interface DRG (0 a : Type) where
  next_bytes : (n : Nat) -> a -> (a, Vect n Bits8)

public export
interface Monad m => MonadRandom (0 m : Type -> Type) where
  random_bytes : (n : Nat) -> m (Vect n Bits8)

public export
{s : _} -> DRG s => MonadRandom (State s) where
  random_bytes n = state (next_bytes n)

public export
next_integer : MonadRandom m => Nat -> m Integer
next_integer bytes = do
  randoms <- random_bytes bytes
  pure $ foldr (\(i,x),a => (shiftL {a=Integer} x i) .|. a) 0 $ zip ((*8) <$> [0..bytes]) (cast <$> toList randoms)

bytes_needed : Integer -> Nat
bytes_needed = (`div` 8) . cast . go 0
  where
    go : Nat -> Integer -> Nat
    go x n = if (n .&. ((bit x) - 1)) == n then x else go (x+8) n

random_num_uniform : MonadRandom m => Nat -> Integer -> m Integer
random_num_uniform bytes min = next_integer bytes >>= (\r => if r >= min then pure r else random_num_uniform bytes min)

public export
uniform_random : MonadRandom m => Integer -> m Integer
uniform_random {m} upper_bound =
  if upper_bound < 0 then negate <$> (uniform_random {m=m} $ abs upper_bound)
    else if upper_bound < 2 then pure 0
      else
        let bytes = bytes_needed upper_bound
        in (`mod` upper_bound) <$> random_num_uniform bytes ((bit bytes) `mod` upper_bound)

public export
uniform_random' : MonadRandom m => Integer -> Integer -> m Integer
uniform_random' {m} lower_bound upper_bound = do
  r <- uniform_random (upper_bound - lower_bound)
  pure (r + lower_bound)

public export
data ChaCha12DRG : Type where
  MkChaCha12DRG : (key : Vect 8 Bits32) -> ChaCha12DRG

public export
new_chacha12_drg : MonadRandom m => m ChaCha12DRG
new_chacha12_drg {m} = (\r => MkChaCha12DRG (from_le <$> group 8 4 r)) <$> (random_bytes {m=m} 32)

chacha12_stream : Vect 8 Bits32 -> Stream Bits8
chacha12_stream key = stream_concat $ map go nats
  where
    go : Nat -> List Bits8
    go iv = toList $ chacha_rfc8439_block 6 (cast iv) key (map (cast . finToNat) range)

public export
DRG ChaCha12DRG where
  next_bytes Z state = (state, [])
  next_bytes bytes (MkChaCha12DRG key) =
    let stream = chacha12_stream key
        key = map (from_le {n=4}) $ group 8 4 $ take 32 stream
        stream = drop 32 stream
    in (MkChaCha12DRG key, take bytes stream)
