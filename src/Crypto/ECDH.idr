module Crypto.ECDH

import Crypto.Random
import Crypto.Curve.XCurves
import Crypto.Curve
import Data.Vect
import Utils.Misc
import Utils.Bytes

public export
interface ECDHCyclicGroup (0 a : Type) where
  Scalar : Type
  Element : Type
  diffie_hellman : Scalar -> Element -> Maybe (List Bits8)
  generate_key_pair : MonadRandom m => m (Scalar,Element)

  deserialize_pk : List Bits8 -> Maybe Element
  serialize_pk : Element -> List Bits8

public export
deserialize_then_dh : ECDHCyclicGroup dh => Scalar {a=dh} -> List Bits8 -> Maybe (List Bits8)
deserialize_then_dh sk pk = (deserialize_pk {a=dh} pk) >>= (diffie_hellman sk)

public export
data X25519_DH : Type where

public export
ECDHCyclicGroup X25519_DH where
  Scalar = Vect 32 Bits8
  Element = Vect 32 Bits8
  diffie_hellman sk pk = map toList (XCurves.mul x25519 sk pk)
  generate_key_pair = do
    sk <- random_bytes 32
    let Just pk = derive_public_key x25519 sk
    | Nothing => generate_key_pair {a=X25519_DH}
    pure (sk,pk)
  deserialize_pk content = exactLength 32 $ fromList content
  serialize_pk = toList

public export
data X448_DH : Type where

public export
ECDHCyclicGroup X448_DH where
  Scalar = Vect 56 Bits8
  Element = Vect 56 Bits8
  diffie_hellman sk pk = map toList (XCurves.mul x448 sk pk)
  generate_key_pair = do
    sk <- random_bytes 56
    let Just pk = derive_public_key x448 sk
    | Nothing => generate_key_pair {a=X448_DH}
    pure (sk,pk)
  deserialize_pk content = exactLength 56 $ fromList content
  serialize_pk = toList

public export
{p : _} -> Point p => ECDHCyclicGroup p where
  Scalar = Integer
  Element = p
  diffie_hellman sk pk = 
    let (x, _) = to_affine $ mul sk pk
        bytes = divCeilNZ (bits {p=p}) 8 SIsNonZero
    in Just $ toList $ integer_to_be bytes x
  generate_key_pair = do
    sk <- uniform_random' 2 (order {p=p} - 1)
    let pk = mul sk $ generator {p=p}
    pure (sk,pk)
  deserialize_pk = decode {p=p}
  serialize_pk = encode {p=p}
