module Crypto.Curve

import Crypto.Random
import Data.Bits
import Utils.Misc

public export
interface Point p where
  to_affine : p -> (Integer, Integer)
  generator : p
  infinity : p
  bits : Nat
  modulus : Integer
  order : Integer

  point_add : p -> p -> p
  mul : Integer -> p -> p

  encode : p -> List Bits8
  decode : List Bits8 -> Maybe p

Point p => Eq p where
  (==) a b = (to_affine a) == (to_affine b)

public export
data ECDSASignature : (p : Type) -> Type where
  MkSignature : (Point p) => p -> (Integer, Integer) -> ECDSASignature p

public export
ecdsa_sign : (Point p, MonadRandom m) => (sk : Integer) -> (msg : Integer) -> m (ECDSASignature p)
ecdsa_sign {p} private_key message = do
  k <- uniform_random' 1 (order {p=p} - 1)
  let public_key = mul private_key generator {p=p}
  let (x, y) = to_affine $ mul k generator {p=p}
  let r = x `mod` (order {p=p})
  let s = mul_mod (inv_mul_mod k $ order {p=p}) (message + (r * private_key)) (order {p=p})
  if (r == 0) || (s == 0)
     then ecdsa_sign {p=p} private_key message
     else pure $ MkSignature public_key (r, s)

public export
ecdsa_verify : Integer -> ECDSASignature p -> Bool
ecdsa_verify message (MkSignature public_key (r, s)) =
  let n = order {p=p}
      s_inv = inv_mul_mod s n
      u1 = mul_mod message s_inv n
      u2 = mul_mod r s_inv n
      pt = point_add (mul u1 generator) (mul u2 public_key)
      (x, _) = to_affine pt
  in (infinity /= pt) && (r `mod'` n) == (x `mod'` n)
