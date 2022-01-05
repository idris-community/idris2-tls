-- BearSSL's "adding holes" algorithm for XOR multiplication
-- Based on BearSSL ghash_ctmul64.c

module Crypto.Hash.GHash

import Utils.Bytes
import Data.Bits
import Data.List
import Data.Vect
import Data.DPair
import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.Nat.Order.Properties
import Utils.Misc
import Crypto.Hash

HValues : Type
HValues = (Bits64, Bits64, Bits64, Bits64, Bits64, Bits64)

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
      (rms 0x0000FFFF0000FFFF 16) $
      (rms 0x00FF00FF00FF00FF 8 ) $
      (rms 0x0F0F0F0F0F0F0F0F 4 ) $
      (rms 0x3333333333333333 2 ) $
      (rms 0x5555555555555555 1 ) x
  in (shiftL x' 32) .|. (shiftR x' 32)

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
      z0h = shiftR (rev64 z0h) 1
      z1h = shiftR (rev64 z1h) 1
      z2h = shiftR (rev64 z2h) 1
      -- Since the operation is done in big-endian, but GHASH spec
      -- needs small endian, we flip the bits
      v0 = z0
      v1 = xor z0h z2
      v2 = xor z1 z2h
      v3 = z1h
      v3 = (shiftL v3 1) .|. (shiftR v2 63)
      v2 = (shiftL v2 1) .|. (shiftR v1 63)
      v1 = (shiftL v1 1) .|. (shiftR v0 63)
      v0 = (shiftL v0 1)
      -- Modular reduction to GF[128]
      v2 = v2 `xor` v0              `xor` (shiftR v0 1)  `xor` (shiftR v0 2) `xor` (shiftR v0 7)
      v1 = v1 `xor` (shiftL v0 63) `xor` (shiftL v0 62) `xor` (shiftL v0 57)
      v3 = v3 `xor` v1             `xor` (shiftR v1 1)  `xor` (shiftR v1 2) `xor` (shiftR v1 7)
      v2 = v2 `xor` (shiftL v1 63) `xor` (shiftL v1 62) `xor` (shiftL v1 57)
  in (v3, v2)

gcm_mult : HValues -> Vect 16 Bits8 -> Vect 16 Bits8
gcm_mult h y =
  let y1 = from_be $ take 8 y
      y0 = from_be $ drop 8 y
      (y1', y0') = gmult_core y1 y0 h
  in to_be {n=8} y1' ++ to_be y0'

mk_h_values : Vect 16 Bits8 -> HValues
mk_h_values h =
  let h1  = from_be $ take 8 h
      h0  = from_be $ drop 8 h
      h0r = rev64 h0
      h1r = rev64 h1
      h2  = xor h0 h1
      h2r = xor h0r h1r
  in (h0, h0r, h1, h1r, h2, h2r)

export
data GHash : Type where
  MkGHash : List Bits8 -> HValues -> Vect 16 Bits8 -> GHash

hash_until_done : GHash -> GHash
hash_until_done ghash@(MkGHash buffer hval state) =
  case splitAtExact 16 buffer of
    Just (a, b) => hash_until_done $ MkGHash b hval (gcm_mult hval (zipWith xor a state))
    Nothing => ghash

export
Digest GHash where
  digest_nbyte = 16
  update message (MkGHash buffer hval state) =
    hash_until_done (MkGHash (buffer <+> message) hval state)
  finalize (MkGHash buffer hval state) =
    let (MkGHash _ _ state) = hash_until_done (MkGHash (pad_zero 16 buffer) hval state)
    in state

export
MAC (Vect 16 Bits8) GHash where
  initialize_mac key = MkGHash [] (mk_h_values key) (replicate _ 0)
