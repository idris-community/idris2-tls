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

some_primes : List Integer
some_primes =
  [ 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73
  , 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157
  , 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241
  , 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347
  , 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439
  , 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547
  , 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643
  , 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751 ]

is_probably_prime : Integer -> Bool
is_probably_prime = go some_primes
  where
    go : List Integer -> Integer -> Bool
    go [] _ = True
    go (p :: xs) n = n `mod` p /= 0 && go xs n

even_component : Integer -> (Integer, Nat)
even_component n = go Z (n-1)
  where
    go : Nat -> Integer -> (Integer, Nat)
    go a n = if not $ testBit n 0 then go (S a) (shiftR n 1) else (n, a)

witness_loop : Integer -> Integer -> Nat -> Integer -> Bool
witness_loop n a r d =
  let x = pow_mod a d n
      alpha = (x == 1) || (x == n - 1)
  in not $ (not alpha) && (go x n a (minus r 1) d)
  where
    go : Integer -> Integer -> Integer -> Nat -> Integer -> Bool
    go x n a Z d = True
    go x n a (S r) d =
      let x' = pow_mod x 2 n
      in (x' /= n - 1) && (go x' n a r d)

miller_test : MonadRandom m => Nat -> Integer -> m Bool
miller_test k n =
  let (d, r) = even_component n
      lnn = log $ cast n
  in (go d r . toList) <$> forM k (uniform_random' 2 (n - 2))
  where
    go : Integer -> Nat -> List Integer -> Bool
    go d r [] = True
    go d r (a :: xs) = witness_loop n a r d && go d r xs

miller_test_rounds : Nat -> Nat
miller_test_rounds n =
  if n <= 1024 then 40
    else if n <= 2048 then 56 else 64

-- TODO: should adjust the value 64 based on how many bits there are for efficency
-- FIPS recommends 40 rounds for 1024 bits, 56 for 2048 bits, 64 for 3072 bits
is_extremely_likely_prime' : MonadRandom m => Nat -> Integer -> m Bool
is_extremely_likely_prime' miller_rounds p =
  if not $ is_probably_prime p then pure False else miller_test miller_rounds p

public export
is_extremely_likely_prime : MonadRandom m => Integer -> m Bool
is_extremely_likely_prime p =
  if p < 2 then pure False
    else if p < 4 then pure True
      else is_extremely_likely_prime' 64 p

generate_big_odd_number : MonadRandom m => Nat -> m Integer
generate_big_odd_number k = do
  r <- next_integer (k `div` 8)
  pure $ r .|. 1

generate_prime' : MonadRandom m => Nat -> Nat -> m Integer
generate_prime' miller_rounds bits = do
  p <- generate_big_odd_number bits
  b <- is_extremely_likely_prime' miller_rounds p
  if b then pure p else generate_prime' miller_rounds bits

public export
generate_prime : MonadRandom m => Nat -> m Integer
generate_prime bits = generate_prime' (miller_test_rounds bits) bits

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
