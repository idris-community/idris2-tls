module Utils.Misc

import Data.Bits
import Data.DPair
import Data.Fin
import Data.List
import Data.Nat
import Data.Nat.Division
import Data.Stream
import Data.Vect
import Data.List1
import Data.Fin.Extra
import Syntax.WithProof

public export
kill_linear : Void -> (1 _ : a) -> s
kill_linear x = void x

public export
subset_to_fin : {a : _} -> Subset Nat (`LT` a) -> Fin a
subset_to_fin (Element x wit) = natToFinLT x {prf = wit}

public export
pair_to_list : (a, a) -> List a
pair_to_list (x1, x2) = [x1, x2]

public export
vect_to_pair : Vect 2 a -> (a, a)
vect_to_pair [x1, x2] = (x1, x2)

public export
pair_to_vect : (a, a) -> Vect 2 a
pair_to_vect (x1, x2) = [x1, x2]

public export
from_vect : Vect 1 a -> a
from_vect [x] = x

public export
to_vect : a -> Vect 1 a
to_vect x = [x]

||| strict version of `(&&)`
public export
s_and : Bool -> Bool -> Bool
s_and True False = False
s_and True True = True
s_and False False = False
s_and False True = False

public export
mmod : Integer -> (m : Nat) -> {auto 0 ok : NonZero m} -> Nat
mmod n m =
  let m' = natToInteger m
  in integerToNat ((m' + n `mod` m') `mod` m')

public export
mod': Integer -> Integer -> Integer
mod' _ 0 = 0
mod' n m = (m + n `mod` m) `mod` m

public export
s_eq : (Bits b, Eq b) => Vect n b -> Vect n b -> Bool
s_eq a b = (zeroBits ==) $ foldr (.|.) zeroBits $ zipWith xor a b

public export
s_eq' : (Bits b, Eq b) => List b -> List b -> Bool
s_eq' a b = (length a == length b) `s_and` ((zeroBits ==) $ foldr (.|.) zeroBits $ zipWith xor a b)

public export
vect_zip_with : {n : Nat} -> {m : Nat} -> (a -> b -> c) -> Vect n a -> Vect m b -> Vect (minimum n m) c
vect_zip_with {n=0} {m} f [] _ = []
vect_zip_with {n} {m=0} f _ [] = rewrite minimumZeroZeroLeft n in []
vect_zip_with f (x::xs) (y::ys) = f x y :: vect_zip_with f xs ys

public export
group : (n : Nat) -> (m : Nat) -> Vect (n * m) a -> Vect n (Vect m a)
group Z     _ _  = []
group (S n) m xs = let (l, r) = splitAt m xs in l :: group n m r

public export
chunk : Nat -> List a -> List (List a)
chunk _ [] = []
chunk n xs = (take n xs) :: (chunk n (drop n xs))

-- https://gist.github.com/buzden/afc798fd2b01388f1626ae58c6ab8548
public export
group' : (n : Nat) -> (m : Nat) -> Vect (n * m) a -> Vect m (Vect n a)
group' n m xs = group m n $ rewrite multCommutative m n in xs

-- https://gist.github.com/buzden/afc798fd2b01388f1626ae58c6ab8548
export
split_at_concat_rev : (n : Nat) -> (xs : Vect (n + m) a) -> {0 l : Vect n a} -> {0 r : Vect m a} -> (0 _ : splitAt n xs = (l, r)) -> l ++ r = xs
split_at_concat_rev Z _ Refl = Refl
split_at_concat_rev (S n) (x::xs) {l} prf with (splitAt n xs) proof sprf
  split_at_concat_rev (S n) (x::xs) {l=x::l} Refl | (l, r) = cong (x::) $ split_at_concat_rev n xs sprf

-- https://gist.github.com/buzden/afc798fd2b01388f1626ae58c6ab8548
public export
concat_group_id : (n : Nat) -> (m : Nat) -> (v : Vect (n * m) a) -> concat (group n m v) = v
concat_group_id Z     _ [] = Refl
concat_group_id (S n) m xs with (splitAt m xs) proof prf
  _ | (l, r) = rewrite concat_group_id n m r in split_at_concat_rev m xs prf

pow_mod' : Integer -> Integer -> Integer -> Integer -> Integer
pow_mod' n x y m =
  if y == 0
     then n
     else let n' = (n * x) `mod` m
              y' = shiftR y 1
              x' = (x * x) `mod` m
          in pow_mod' (if testBit y 0 then n' else n) x' y' m

public export
pow_mod : Integer -> Integer -> Integer -> Integer
pow_mod x y m = pow_mod' 1 (x `mod'` m) (y `mod'` m) m

mul_mod' : Integer -> Integer -> Integer -> Integer -> Integer
mul_mod' n x y m =
  if y == 0
     then n
     else let n' = (n + x) `mod` m
              y' = shiftR y 1
              x' = (x * 2) `mod` m
          in mul_mod' (if testBit y 0 then n' else n) x' y' m

public export
mul_mod : Integer -> Integer -> Integer -> Integer
mul_mod x y m = mul_mod' 0 (x `mod'` m) (y `mod'` m) m

public export
quot_rem : Integer -> Integer -> (Integer, Integer)
quot_rem val d =
  let dividend = if d < 0 then -(val `div` abs d) else val `div` d
      remainder = abs (val - dividend * d)
  in (dividend, remainder)

public export
gcd' : Integer -> Integer -> Integer
gcd' a 0 = a
gcd' a b = gcd' b (a `mod` b)

public export
are_coprimes : Integer -> Integer -> Bool
are_coprimes x y = (gcd' x y) == 1

-- Extended Euclidean Algorithm
-- Only valid when gcd(a, b) = 1
public export
extended_gcd : Integer -> Integer -> (Integer, Integer)
extended_gcd a 0 = (1, 0)
extended_gcd a b =
  let (q, r) = quot_rem a b
      (s, t) = extended_gcd b r
  in (t, s - q * t)

-- Only valid when gcd(a, b) = 1
public export
inv_mul_mod : Integer -> Integer -> Integer
inv_mul_mod a m =
  let (x, y) = extended_gcd a m
  in mod' x m

public export
forM : Applicative f => (n : Nat) -> (f b) -> f (Vect n b)
forM n f = for (the (Vect n (Fin n)) range) (const f)

utf8_bytelen : Bits8 -> Maybe (Bits8, Nat)
utf8_bytelen x =
  if (x .&. 0b01111111) == x then Just (x, 0) -- ascii
    else if (shiftR x 5) == 0b110   then Just (x .&. 0b0011111, 1)
    else if (shiftR x 4) == 0b1110  then Just (x .&. 0b0001111, 2)
    else if (shiftR x 3) == 0b11110 then Just (x .&. 0b0000111, 3)
    else Nothing

utf8_unmask : Bits8 -> Maybe Bits8
utf8_unmask x = const (x .&. 0b00111111) <$> guard (shiftR x 6 == 0b10)

utf8_pushbits : Integer -> List Bits8 -> Integer
utf8_pushbits acc [] = acc
utf8_pushbits acc (x::xs) = utf8_pushbits ((shiftL acc 6) .|. (cast x)) xs

public export
utf8_decode : List Bits8 -> Maybe String
utf8_decode = go []
  where
    go : List Char -> List Bits8 -> Maybe String
    go acc [] = Just $ pack $ reverse acc
    go acc (x :: xs) = do
      (x, l) <- utf8_bytelen x
      let (y,ys) = splitAt l xs
      guard (length y == l)
      y <- traverse utf8_unmask y
      let c = utf8_pushbits (cast x) y
      go ((cast c) :: acc) ys

public export
stream_concat : Foldable t => Stream (t a) -> Stream a
stream_concat = go . map toList
  where
    go : Stream (List a) -> Stream a
    go ([] :: ys) = stream_concat ys
    go ((x :: xs) :: ys) = x :: stream_concat (xs :: ys)

public export
ok_minus : (n : Nat) -> (m : Nat) -> LTE m n -> Nat
ok_minus n Z LTEZero = n
ok_minus (S n) (S m) (LTESucc wit) = ok_minus n m wit

namespace List
  public export
  enumerate : Nat -> List a -> List (Nat, a)
  enumerate n [] = []
  enumerate n (x :: xs) = (n, x) :: enumerate (S n) xs

namespace Vect
  public export
  replace_vect : (0 _ : n = m) -> Vect n a -> Vect m a
  replace_vect prf input = rewrite sym prf in input

  public export
  cycle : Vect (S n) a -> Stream a
  cycle xs = go xs
    where
    go : Vect i a -> Stream a
    go [] = go xs
    go (z :: zs) = z :: go zs

  public export
  unsnoc : Vect (S n) a -> (Vect n a, a)
  unsnoc (x :: []) = ([], x)
  unsnoc (x :: (y :: ys)) = let (zs, z) = unsnoc (y :: ys) in (x :: zs, z)

namespace Stream
  public export
  prepend : List a -> Stream a -> Stream a
  prepend [] ys = ys
  prepend (x :: xs) ys = x :: prepend xs ys

  public export
  duplicate : Stream a -> Stream (Stream a)
  duplicate (x :: xs) = (x :: xs) :: duplicate xs

  public export
  split : (n : Nat) -> Stream a -> (Vect n a, Stream a)
  split Z xs = ([], xs)
  split (S n) (v :: xs) = let (vs, xs') = split n xs in (v :: vs, xs')

  public export
  chunk : (n : Nat) -> Stream a -> Stream (Vect n a)
  chunk n xs = let (y, ys) = split n xs in y :: chunk n ys

public export
lte_plus_left : (a : _) -> LTE (a + b) c -> LTE b c
lte_plus_left Z x = x
lte_plus_left (S k) x = lte_plus_left k (lteSuccLeft x)

public export
maybe_to_either : Maybe a -> Lazy b -> Either b a
maybe_to_either Nothing b = Left $ force b
maybe_to_either (Just a) _ = Right a

public export
init' : List a -> List a
init' [] = []
init' (x :: xs) = init (x :: xs)

public export
uncons1 : List1 a -> (List a, a)
uncons1 lst = (init lst, last lst)

public export
splitAt : (n : Nat) -> Stream a -> (Vect n a, Stream a)
splitAt n s = (take n s, drop n s)

public export
zeros : {n : Nat} -> Vect n Bits8
zeros = map (const 0) Fin.range

public export
splitLastAt1 : (n : Nat) -> List a -> Maybe (List1 a, Vect n a)
splitLastAt1 n v = do
  let m = minus (length v) n
  let (a, b) = splitAt m v
  a' <- fromList a
  b' <- exactLength n $ fromList b
  pure (a', b')

public export
modFinNZ : Nat -> (b : Nat) -> NonZero b -> Fin b
modFinNZ a b prf = let x = boundModNatNZ a b prf in natToFinLTE (modNatNZ a b prf) x

public export
collapse_ordering : List Ordering -> Ordering
collapse_ordering (LT :: xs) = LT
collapse_ordering (GT :: xs) = GT
collapse_ordering (EQ :: xs) = collapse_ordering xs
collapse_ordering [] = EQ

