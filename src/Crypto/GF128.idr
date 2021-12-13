-- BearSSL's "adding holes" algorithm for XOR multiplication
-- Based on BearSSL ghash_ctmul64.c

module Crypto.GF128

import Control.Algebra

import Utils.Bytes

import Data.Bits
import Data.Vect
import Data.DPair
import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.Nat.Order.Properties

public export
data F128 : Type where
  MkF128 : Vect 16 Bits8 -> F128

public export
HValues : Type
HValues = (Bits64, Bits64, Bits64, Bits64, Bits64, Bits64)

public export
Eq F128 where
  (==) (MkF128 a) (MkF128 b) = a == b

public export
Show F128 where
  show (MkF128 x) = xxd $ toList x

public export
xor : F128 -> F128 -> F128
xor (MkF128 x) (MkF128 y) = MkF128 $ zipWith xor x y

public export
zero : F128
zero = MkF128 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- Carryless multiplication with "holes"
bmul : Bits64 -> Bits64 -> Bits64
bmul x y =
  let x0 = x .&. 0x1111111111111111
      x1 = x .&. 0x2222222222222222
      x2 = x .&. 0x4444444444444444
      x3 = x .&. 0x8888888888888888
      y0 = y .&. 0x1111111111111111
      y1 = y .&. 0x2222222222222222
      y2 = y .&. 0x4444444444444444
      y3 = y .&. 0x8888888888888888
      z0 = (x0 * y0) `xor` (x1 * y3) `xor` (x2 * y2) `xor` (x3 * y1)
      z1 = (x0 * y1) `xor` (x1 * y0) `xor` (x2 * y3) `xor` (x3 * y2)
      z2 = (x0 * y2) `xor` (x1 * y1) `xor` (x2 * y0) `xor` (x3 * y3)
      z3 = (x0 * y3) `xor` (x1 * y2) `xor` (x2 * y1) `xor` (x3 * y0)
  in (z0 .&. 0x1111111111111111) .|.
     (z1 .&. 0x2222222222222222) .|.
     (z2 .&. 0x4444444444444444) .|.
     (z3 .&. 0x8888888888888888)

rms : Bits64 -> Index {a=Bits64} -> Bits64 -> Bits64
rms m s x = (shiftL (x .&. m) s) .|. ((shiftR x s) .&. m)

rev64 : Bits64 -> Bits64
rev64 x =
  let x' =
      (rms 0x0000FFFF0000FFFF (Element 16 $ lteAddRight _)) $
      (rms 0x00FF00FF00FF00FF (Element 8  $ lteAddRight _)) $
      (rms 0x0F0F0F0F0F0F0F0F (Element 4  $ lteAddRight _)) $
      (rms 0x3333333333333333 (Element 2  $ lteAddRight _)) $
      (rms 0x5555555555555555 (Element 1  $ lteAddRight _)) x
  in (shiftL x' $ Element 32 $ lteAddRight _) .|. (shiftR x' $ Element 32 $ lteAddRight _)

-- Take the indexes out or it will take forever to compile gmult_core
i1 : Index {a=Bits64}
i1  = Element 1 $ lteAddRight _
i2 : Index {a=Bits64}
i2  = Element 2 $ lteAddRight _
i7 : Index {a=Bits64}
i7  = Element 7 $ lteAddRight _
i63 : Index {a=Bits64}
i63 = Element 63 $ lteAddRight _
i62 : Index {a=Bits64}
i62 = Element 62 $ lteAddRight _
i57 : Index {a=Bits64}
i57 = Element 57 $ lteAddRight _

gmult_core : Bits64 -> Bits64 -> HValues -> (Bits64, Bits64)
gmult_core y1 y0 (h0, h0r, h1, h1r, h2, h2r) =
  let y1r = rev64 y1
      y0r = rev64 y0
      y2 = xor y0 y1
      y2r = xor y0r y1r
      -- Karatsuba decomposition
      -- Here we decompose the 128 bit multiplication into
      -- 3 64-bits multiplication
      -- The h-suffixed variables are just multiplication for
      -- reversed bits, which is necessary because we want the
      -- high bits
      z0 = bmul y0 h0
      z1 = bmul y1 h1
      z2 = bmul y2 h2
      z0h = bmul y0r h0r
      z1h = bmul y1r h1r
      z2h = bmul y2r h2r
      z2  = xor (xor z0 z1) z2
      z2h = xor (xor z0h z1h) z2h
      z0h = shiftR (rev64 z0h) i1
      z1h = shiftR (rev64 z1h) i1
      z2h = shiftR (rev64 z2h) i1
      -- Since the operation is done in big-endian, but GHASH spec
      -- needs small endian, we flip the bits
      v0 = z0
      v1 = xor z0h z2
      v2 = xor z1 z2h
      v3 = z1h
      v3 = (shiftL v3 i1) .|. (shiftR v2 i63)
      v2 = (shiftL v2 i1) .|. (shiftR v1 i63)
      v1 = (shiftL v1 i1) .|. (shiftR v0 i63)
      v0 = (shiftL v0 i1)
      -- Modular reduction to GF[128]
      v2 = v2 `xor` v0              `xor` (shiftR v0 i1)  `xor` (shiftR v0 i2) `xor` (shiftR v0 i7)
      v1 = v1 `xor` (shiftL v0 i63) `xor` (shiftL v0 i62) `xor` (shiftL v0 i57) 
      v3 = v3 `xor` v1              `xor` (shiftR v1 i1)  `xor` (shiftR v1 i2) `xor` (shiftR v1 i7)  
      v2 = v2 `xor` (shiftL v1 i63) `xor` (shiftL v1 i62) `xor` (shiftL v1 i57) 
  in (v3, v2)

export
gcm_mult : HValues -> F128 -> F128
gcm_mult h (MkF128 y) =
  let y1 = from_be $ take 8 y
      y0 = from_be $ drop 8 y
      (y1', y0') = gmult_core y1 y0 h
  in MkF128 $ to_be {n=8} y1' ++ to_be y0'

export
mk_h_values : F128 -> HValues
mk_h_values (MkF128 h) =
  let h1  = from_be $ take 8 h
      h0  = from_be $ drop 8 h
      h0r = rev64 h0
      h1r = rev64 h1
      h2  = xor h0 h1
      h2r = xor h0r h1r
  in (h0, h0r, h1, h1r, h2, h2r)
