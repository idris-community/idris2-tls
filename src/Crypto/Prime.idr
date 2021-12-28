module Crypto.Prime

import Crypto.Random
import Data.Bits
import Utils.Misc
import Data.Vect
import Data.Stream

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
  in if (x == 1) || (x == n - 1) then True else not (go x n a (pred r) d)
  where
    go : Integer -> Integer -> Integer -> Nat -> Integer -> Bool
    go x n a Z d = True
    go x n a (S r) d =
      let x' = pow_mod x 2 n
      in (x' /= n - 1) && (go x' n a r d)

miller_test : MonadRandom m => Nat -> Integer -> m Bool
miller_test k n =
  let (d, r) = even_component n
  in (go d r . toList) <$> forM k (uniform_random' 2 (n - 2))
  where
    go : Integer -> Nat -> List Integer -> Bool
    go d r [] = True
    go d r (a :: xs) = witness_loop n a r d && go d r xs

miller_test_rounds : Nat -> Nat
miller_test_rounds n =
  if n <= 1024 then 40
    else if n <= 2048 then 56 else 64

-- Does not perform check on p < 751 correctly
is_extremely_likely_prime' : MonadRandom m => Nat -> Integer -> m Bool
is_extremely_likely_prime' miller_rounds p =
  if not $ is_probably_prime p then pure False else miller_test miller_rounds p

public export
is_extremely_likely_prime : MonadRandom m => Integer -> m Bool
is_extremely_likely_prime p =
  if p < 2 then pure False
    else if (p < 4) || (p `elem` some_primes) then pure True
      else is_extremely_likely_prime' 64 p

generate_big_odd_number : MonadRandom m => Nat -> m Integer
generate_big_odd_number k = do
  r <- next_integer (k `div` 8)
  pure $ r .|. setBit 1 k

public export
generate_prime : MonadRandom m => Nat -> m Integer
generate_prime bits = do
  let rounds = miller_test_rounds bits
  seed <- generate_big_odd_number bits
  (if seed < 1000 then go_small else go) rounds seed
  where
    go : Nat -> Integer -> m Integer
    go rounds x = (is_extremely_likely_prime' rounds x) >>= (\y => if y then pure x else go rounds (x + 2))
    go_small : Nat -> Integer -> m Integer
    go_small rounds x = (is_extremely_likely_prime x) >>= (\y => if y then pure x else go_small rounds (x + 2))
