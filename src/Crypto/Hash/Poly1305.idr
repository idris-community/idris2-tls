-- Implementation based on https://www.newspipe.org/article/public/309714

module Crypto.Hash.Poly1305

import Data.Vect
import Utils.Misc
import Utils.Bytes
import Data.Bits
import Crypto.Hash

export
record Poly1305 where
  constructor MkPoly1305
  buffer : List Bits8
  h : Vect 3 Bits64
  r : Vect 2 Bits64
  s : Vect 2 Bits64

record Bits128 where
  constructor MkBits128
  lo : Bits64
  hi : Bits64

bits128_to_integer : Bits128 -> Integer
bits128_to_integer b = (cast b.lo) .|. (shiftL (cast b.hi) 64)

mask_low_2_bits : Bits64
mask_low_2_bits  = 0x0000000000000003

mask_not_low_2_bits : Bits64
mask_not_low_2_bits = complement mask_low_2_bits

p0 : Bits64
p0 = 0xFFFFFFFFFFFFFFFB

p1 : Bits64
p1 = 0xFFFFFFFFFFFFFFFF

p2 : Bits64
p2 = 0x0000000000000003

add64 : Bits64 -> Bits64 -> Bits64 -> (Bits64, Bits64)
add64 x y carry =
  let sum = x + y + carry
      carry = shiftR ((x .&. y) .|. ((x .|. y) .&. (complement sum))) 63
  in (sum, carry)

sub64 : Bits64 -> Bits64 -> Bits64 -> (Bits64, Bits64)
sub64 x y borrow =
  let diff = x - y - borrow
      borrow_out = shiftR ((complement x .&. y) .|. (diff .&. complement (x `xor` y))) 63
  in (diff, borrow_out)

mul64_mask32 : Bits64
mul64_mask32 = cast (the Bits32 oneBits)

mul64 : Bits64 -> Bits64 -> Bits128
mul64 x y =
  let x0 = x .&. mul64_mask32
      x1 = shiftR x 32
      y0 = y .&. mul64_mask32
      y1 = shiftR y 32
      w0 = x0 * y0
      t = (x1 * y0) + (shiftR w0 32)
      w1 = t .&. mul64_mask32
      w2 = shiftR t 32
      w1 = w1 + (x0 * y1)
  in MkBits128 (x * y) (x1 * y1 + w2 + (shiftR w1 32))

add128 : Bits128 -> Bits128 -> Bits128
add128 a b =
  let (lo, c) = add64 a.lo b.lo 0
      (hi, _) = add64 a.hi b.hi c
  in MkBits128 lo hi

shiftr2 : Bits128 -> Bits128
shiftr2 a = MkBits128 ((shiftR a.lo 2) .|. (shiftL (a.hi .&. 3) 62)) (shiftR a.hi 2)

-- select64 returns x if v == 1 and y if v == 0, in constant time
select64 : Bits64 -> Bits64 -> Bits64 -> Bits64
select64 v x y = (x .&. complement (v - 1)) .|. (y .&. (v - 1))

core : Poly1305 -> Bits64 -> Bits64 -> Bits64 -> (Bits64, Bits64, Bits64)
core state h0 h1 h2 =
  let [r0, r1] = state.r

      h0r0 = mul64 h0 r0
      h1r0 = mul64 h1 r0
      h2r0 = mul64 h2 r0
      h0r1 = mul64 h0 r1
      h1r1 = mul64 h1 r1
      h2r1 = mul64 h2 r1

      m0 = h0r0
      m1 = add128 h1r0 h0r1
      m2 = add128 h2r0 h1r1
      m3 = h2r1

      t0 = m0.lo
      (t1, c) = add64 m1.lo m0.hi 0
      (t2, c) = add64 m2.lo m1.hi c
      (t3, _) = add64 m3.lo m2.hi c

      h0 = t0
      h1 = t1
      h2 = t2 .&. mask_low_2_bits
      cc = MkBits128 (t2 .&. mask_not_low_2_bits) t3

      (h0, c) = add64 h0 cc.lo 0
      (h1, c) = add64 h1 cc.hi c
      h2 = h2 + c

      cc = shiftr2 cc

      (h0, c) = add64 h0 cc.lo 0
      (h1, c) = add64 h1 cc.hi c
      h2 = h2 + c
  in (h0, h1, h2)

update' : Poly1305 -> Poly1305
update' state =
  case splitAtExact 16 state.buffer of
    Just (buf, rest) =>
      let (a, b) = bimap from_le from_le (splitAt 8 buf)
          [h0, h1, h2] = state.h
          (h0, c) = add64 h0 a 0
          (h1, c) = add64 h1 b c
          h2 = h2 + c + 1
          (h0, h1, h2) = core state h0 h1 h2
      in {h := [h0, h1, h2]} state
    Nothing => state

finalize' : Poly1305 -> Vect 16 Bits8
finalize' state =
  case exactLength 16 (fromList state.buffer) of
    Just buf =>
      let (a, b) = bimap from_le from_le (splitAt 8 buf)
          [h0, h1, h2] = state.h
          (h0, c) = add64 h0 a 0
          (h1, c) = add64 h1 b c
          h2 = h2 + c
          (h0, h1, h2) = core state h0 h1 h2

          (t0, b) = sub64 h0 p0 0
          (t1, b) = sub64 h1 p1 b
          (_ , b) = sub64 h2 p2 b

          h0 = select64 b h0 t0
          h1 = select64 b h1 t1

          [s0, s1] = state.s
          (h0, c) = add64 h0 s0 0
          (h1, _) = add64 h1 s1 c
      in to_le {n=8} h0 ++ to_le {n=8} h1
    Nothing =>
      finalize' $ { buffer := pad_zero 16 (state.buffer <+> [ 0x01 ]) } (update' state)

export
Digest Poly1305 where
  digest_nbyte = 16
  update message state = update' $ {buffer := state.buffer <+> message} state
  finalize = finalize'

export
MAC (Vect 32 Bits8) Poly1305 where
  initialize_mac key =
    let ([r0, r1], s) = splitAt 2 $ map from_le $ group 4 8 key
        r0 = r0 .&. 0x0FFFFFFC0FFFFFFF
        r1 = r1 .&. 0x0FFFFFFC0FFFFFFC
    in MkPoly1305 [] [0,0,0] [r0, r1] s
