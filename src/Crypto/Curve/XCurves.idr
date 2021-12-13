module Crypto.Curve.XCurves

-- This doesn't implement the Point interface because I can't be bothered will implementing
-- point addition. This module is for DH strictly.

import Data.Bits
import Data.Bool.Xor
import Data.Vect
import Debug.Trace
import Utils.Bytes
import Utils.Misc

data XCurvesParameter : (n : Nat) -> Type where
  XCParam : {n : Nat} -> 
            (bits : Nat) -> 
            (u : Integer) -> 
            (a24 : Integer) -> 
            (scalar_decoder : Vect n Bits8 -> Integer) -> 
            (prime : Integer) ->
            XCurvesParameter n

cswap : Integer -> Integer -> Integer -> (Integer, Integer)
cswap swap x2 x3 = 
  let dummy = (0 - swap) .&. (x2 `xor` x3)
  in (x2 `xor` dummy, x3 `xor` dummy)

mul_go : {n : Nat} -> XCurvesParameter n -> Integer -> Integer -> Integer -> Integer -> Integer -> Integer -> Integer -> Nat -> 
         (Integer, Integer, Integer, Integer, Integer)
mul_go param@(XCParam _ _ a24 _ prime) x1 x2 z2 x3 z3 swap k t =
  let mul = (\a,b => mul_mod a b prime)
      pow = (\a,b => pow_mod a b prime)
      k_t = (shiftR k t) .&. 1
      swap' = xor swap k_t
      (x2, x3) = cswap swap' x2 x3
      (z2, z3) = cswap swap' z2 z3
      a = x2 + z2
      aa = a `mul` a
      b = x2 - z2
      bb = b `mul` b
      e = aa - bb
      c = x3 + z3
      d = x3 - z3
      da = d `mul` a
      cb = c `mul` b
      x3 = pow (da + cb) 2
      z3 = x1 `mul` (pow (da - cb) 2)
      x2 = aa `mul` bb
      z2 = e `mul` (aa + (a24 `mul` e))
  in case t of
       Z => (x2, x3, z2, z3, k_t)
       S t' => mul_go param x1 x2 z2 x3 z3 k_t k t'

public export
mul : {n : Nat} -> XCurvesParameter n -> Vect n Bits8 -> Vect n Bits8 -> Maybe (Vect n Bits8)
mul {n} param@(XCParam bits _ a24 decode prime) k u = 
  let u' = le_to_integer u
      k' = decode k
      (x2, x3, z2, z3, swap) = mul_go param u' 1 0 u' 1 0 k' (minus bits 1)
      (x2', x3') = cswap swap x2 x3
      (z2', z3') = cswap swap z2 z3
      beta = pow_mod z2' (prime-2) prime
      secret = mul_mod x2' beta prime
  in guard (secret /= 0) *> (pure $ integer_to_le _ secret )

generator : {n : Nat} -> XCurvesParameter n -> Vect n Bits8
generator (XCParam _ u _ _ _) = integer_to_le _ u

public export
derive_public_key : {n : Nat} -> XCurvesParameter n -> Vect n Bits8 -> Maybe (Vect n Bits8)
derive_public_key param k = mul param k $ generator param

decode_scalar_25519 : Vect 32 Bits8 -> Integer
decode_scalar_25519 =
  le_to_integer
  . updateAt 0  (.&. 248) 
  . updateAt 31 (.&. 127)
  . updateAt 31 (.|.  64) 

decode_scalar_448 : Vect 56 Bits8 -> Integer
decode_scalar_448 =
  le_to_integer
  . updateAt 0  (.&. 252) 
  . updateAt 55 (.|. 128) 

public export
x25519 : XCurvesParameter 32
x25519 = XCParam 255 9 121665 decode_scalar_25519 $ (bit 255) - 19

public export
x448 : XCurvesParameter 56
x448 = XCParam 448 5 39081 decode_scalar_448 $ (bit 448) - (bit 224) - 1
