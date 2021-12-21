module Crypto.Curve.Weierstrass

import Crypto.Curve
import Data.Bits
import Data.List
import Data.Vect
import Utils.Bytes
import Utils.Misc

-- Weiserstrass curve y^2 = x^3 + ax + b in Jacobian coordinate
public export
interface WeierstrassPoint p where
  a_coefficent : Integer
  b_coefficent : Integer
  prime : Integer -- If this isn't prime the skinwalker will devour you
  to_jacobian : p -> (Integer, Integer, Integer)
  from_jacobian : (Integer, Integer, Integer) -> p
  g : p
  to_from_jacobian : (x : (Integer, Integer, Integer)) -> to_jacobian (from_jacobian x) = x
  bits' : Nat
  curve_n : Integer

j_point_double : WeierstrassPoint p => (Integer, Integer, Integer) -> (Integer, Integer, Integer)
j_point_double (x, y, z) =
  let modulus = prime {p=p}
      s  = (4 * x * y * y) `mod'` modulus
      z4 = pow_mod z 4 modulus
      y4 = pow_mod y 4 modulus
      m  = (3 * x * x + a_coefficent {p} * z4) `mod'` modulus
      x' = (m * m - 2 * s) `mod'` modulus
      y' = (m * (s - x') - 8 * y4) `mod'` modulus
      z' = (2 * y * z) `mod'` modulus
  in (x', y', z')

j_point_add : WeierstrassPoint p => (Integer, Integer, Integer) -> (Integer, Integer, Integer) -> (Integer, Integer, Integer)
j_point_add (x, y, 0) b = b
j_point_add a (x, y, 0) = a
j_point_add a@(xp, yp, zp) b@(xq, yq, zq) =
  let m = prime {p=p}
      zq2 = pow_mod zq 2 m
      zq3 = pow_mod zq 3 m
      zp2 = pow_mod zp 2 m
      zp3 = pow_mod zp 3 m
      u1 = mul_mod xp zq2 m
      u2 = mul_mod xq zp2 m
      s1 = mul_mod yp zq3 m
      s2 = mul_mod yq zp3 m
      h = u2 - u1
      r = s2 - s1
      h2 = pow_mod h 2 m
      h3 = mul_mod h h2 m
      u1h2 = mul_mod u1 h2 m
      nx = ((r * r) - h3 - 2 * u1h2) `mod'` m
      ny = (r * (u1h2 - nx) - s1 * h3) `mod'` m
      nz = (h * zp * zq) `mod'` m
      in if h == 0 then (if r == 0 then j_point_double {p=p} a else (0, 1, 0)) else (nx, ny, nz)

point_double : (Point p, WeierstrassPoint p) => p -> p
point_double b = from_jacobian {p=p} (j_point_double {p=p} (to_jacobian b))

mul' : (Point p, WeierstrassPoint p) => p -> p -> Nat -> Integer -> p
mul' r0 r1 m d =
  let (r0', r1') = if testBit d m then (point_add r0 r1, point_double r1) else (point_double r0, point_add r0 r1)
  in case m of
       S m' => mul' r0' r1' m' d
       Z => r0'

public export
WeierstrassPoint p => Point p where
  infinity = from_jacobian (0, 1, 0)
  generator = g
  bits = bits' {p=p}
  to_affine point =
    let (x, y, z) = to_jacobian point
        m = prime {p=p}
        z' = inv_mul_mod z m
        z2 = z' * z'
        z3 = z2 * z'
    in (mul_mod x z2 m, mul_mod y z3 m)
  modulus = prime {p=p}
  order = curve_n {p=p}
  point_add a b = from_jacobian {p=p} (j_point_add {p=p} (to_jacobian a) (to_jacobian b))
  mul s pt = mul' infinity pt (bits {p=p}) s

  encode point =
    let bytes = (7 + bits {p=p}) `div` 8
        (x', y') = to_affine point
        x = toList $ integer_to_be bytes x'
        y = toList $ integer_to_be bytes y'
    in 4 :: (x <+> y)

  decode (4 :: body) = do
    let bytes = (7 + bits {p=p}) `div` 8
    let (x', y') = splitAt bytes body
    x <- map be_to_integer $ exactLength bytes $ fromList x'
    y <- map be_to_integer $ exactLength bytes $ fromList y'

    -- infinity check
    guard $ not $ (x == 0) && (y == 0)

    -- check on curve
    let pri = modulus {p=p}
    let lhs = pow_mod y 2 pri
    let a   = a_coefficent {p=p}
    let b   = b_coefficent {p=p}
    let rhs = ((pow_mod x 3 pri) + (mul_mod x a pri) + b) `mod'` pri
    guard $ lhs == rhs

    pure $ from_jacobian (x, y, 1)
  decode _ = Nothing

public export
data P256 : Type where
  MkP256 : (Integer, Integer, Integer) -> P256

public export
WeierstrassPoint P256 where
  prime =
    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
  a_coefficent =
    0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc
  b_coefficent =
    0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  from_jacobian = MkP256
  to_jacobian (MkP256 p) = p
  g = MkP256
    ( 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
    , 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
    , 1 )
  to_from_jacobian x = Refl
  bits' = 256
  curve_n =
    0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

public export
data P384 : Type where
  MkP384 : (Integer, Integer, Integer) -> P384

public export
WeierstrassPoint P384 where
  prime =
    0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
  a_coefficent =
    0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc
  b_coefficent =
    0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
  from_jacobian = MkP384
  to_jacobian (MkP384 p) = p
  g = MkP384
    ( 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
    , 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
    , 1 )
  to_from_jacobian x = Refl
  bits' = 384
  curve_n =
    0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973

public export
data P521 : Type where
  MkP521 : (Integer, Integer, Integer) -> P521

public export
WeierstrassPoint P521 where
  prime =
    0x01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  a_coefficent =
    0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc
  b_coefficent =
    0x0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00
  from_jacobian = MkP521
  to_jacobian (MkP521 p) = p
  g = MkP521
    ( 0x00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66
    , 0x011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650
    , 1 )
  to_from_jacobian x = Refl
  bits' = 521
  curve_n =
    0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409

