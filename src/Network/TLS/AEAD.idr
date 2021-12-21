module Network.TLS.AEAD

import Data.Stream
import Data.Bits
import Data.Vect
import Data.List
import Utils.Misc
import Utils.Bytes
import Crypto.AES
import Crypto.GF128
import Crypto.ChaCha

public export
interface AEAD (0 a : Type) where
  iv_bytes : Nat
  key_bytes : Nat
  mac_bytes : Nat
  keystream : Vect key_bytes Bits8 -> Vect iv_bytes Bits8 -> Stream Bits8
  create_aad : Vect key_bytes Bits8 -> Vect iv_bytes Bits8 -> (aad : List Bits8) -> List Bits8 -> Vect mac_bytes Bits8

  tls12_iv_bytes : Nat
  tls12_explicit_iv_bytes : Nat
  tls12_derive_iv : (sequence : Nat) -> (tls12_iv : Vect tls12_iv_bytes Bits8) -> (Vect tls12_explicit_iv_bytes Bits8, Vect iv_bytes Bits8)

public export
encrypt : AEAD a => Vect (key_bytes {a=a}) Bits8 -> Vect (iv_bytes {a=a}) Bits8 ->
          List Bits8 -> List Bits8 -> (List Bits8, Vect (mac_bytes {a=a}) Bits8)
encrypt {a} key iv plaintext aad =
  let ciphertext = zipWith xor plaintext (toList $ Stream.take (length plaintext) $ keystream key iv)
      mac_tag = create_aad key iv aad ciphertext
  in (ciphertext, mac_tag)

public export
decrypt : AEAD a => Vect (key_bytes {a=a}) Bits8 -> Vect (iv_bytes {a=a}) Bits8 ->
          List Bits8 -> List Bits8 -> List Bits8 -> (List Bits8, Bool)
decrypt {a} key iv ciphertext aad mac_tag' =
  let plaintext = zipWith xor ciphertext (toList $ Stream.take (length ciphertext) $ keystream key iv)
      mac_tag = create_aad key iv aad ciphertext
  in (plaintext, s_eq' (toList mac_tag) mac_tag')

aes_pad_iv_block : {iv : Nat} -> Vect iv Bits8 -> Stream (Vect (iv+4) Bits8)
aes_pad_iv_block iv = map ((iv ++) . to_be . (cast {to=Bits32})) $ drop 2 nats

pad : Nat -> List Bits8 -> List Bits8
pad Z a = a
pad (S n) a =
  let l = length a
      l = minus ((S n) * (divCeilNZ l (S n) SIsNonZero)) l
  in a <+> replicate l 0

toF128 : List Bits8 -> F128
toF128 elem =
  case exactLength 16 $ fromList $ take 16 elem of
    Just v => MkF128 v
    Nothing => toF128 (pad 16 elem)

public export
data AES_128_GCM : Type where

public export
AEAD AES_128_GCM where
  iv_bytes = 12
  key_bytes = 16
  mac_bytes = 16
  keystream key iv =
    let key' = group 4 4 key
    in stream_concat $ map (toList . Vect.concat . encrypt_block AES128 key' . group 4 4) (aes_pad_iv_block iv)
  create_aad key iv aad ciphertext =
    let key' = group 4 4 key
        a = toList $ to_be {n=8} $ cast {to=Bits64} $ 8 * (length aad)
        c = toList $ to_be {n=8} $ cast {to=Bits64} $ 8 * (length ciphertext)
        input = chunk 16 (pad 16 aad <+> pad 16 ciphertext <+> a <+> c)
        h = mk_h_values
          $ MkF128
          $ concat
          $ encrypt_block AES128 key'
          $ group 4 4 
          $ map (const 0)
          $ Fin.range
        MkF128 output = foldl (\e,a => gcm_mult h $ xor a e) zero $ map toF128 input
        j0 = concat $ encrypt_block AES128 key' $ group 4 4 (iv ++ (to_be $ the Bits32 1))
    in zipWith xor j0 output

  tls12_iv_bytes = 4
  tls12_explicit_iv_bytes = 8
  tls12_derive_iv sequence iv =
    let eiv = integer_to_be 8 $ cast sequence
    in (eiv, iv ++ eiv)

-- TODO: fix and test them
public export
data AES_256_GCM : Type where

public export
AEAD AES_256_GCM where
  iv_bytes = 12
  key_bytes = 32
  mac_bytes = 16
  keystream key iv =
    let key' = group 8 4 key
    in stream_concat $ map (toList . Vect.concat . encrypt_block AES256 key' . group 4 4) (aes_pad_iv_block iv)
  create_aad key iv aad ciphertext =
    let key' = group 8 4 key
        a = toList $ to_be {n=8} $ cast {to=Bits64} $ 8 * (length aad)
        c = toList $ to_be {n=8} $ cast {to=Bits64} $ 8 * (length ciphertext)
        input = chunk 16 (pad 16 aad <+> pad 16 ciphertext <+> a <+> c)
        h = mk_h_values 
          $ MkF128 
          $ concat 
          $ encrypt_block AES256 key' 
          $ group 4 4 
          $ map (const 0) 
          $ Fin.range
        MkF128 output = foldl (\e,a => gcm_mult h $ xor a e) zero $ map toF128 input
        j0 = concat $ encrypt_block AES256 key' $ group 4 4 (iv ++ (to_be $ the Bits32 1))
    in zipWith xor j0 output

  tls12_iv_bytes = 4
  tls12_explicit_iv_bytes = 8
  tls12_derive_iv sequence iv =
    let eiv = integer_to_be 8 $ cast sequence
    in (eiv, iv ++ eiv)

{-
public export
data ChaCha20_Poly1305 : Type where

clamp : Integer -> Integer
clamp r = r .&. 0x0ffffffc0ffffffc0ffffffc0fffffff

poly1305_prime : Integer
poly1305_prime = 0x3fffffffffffffffffffffffffffffffb

public export
AEAD ChaCha20_Poly1305 where
  iv_bytes = 12
  tls12_iv_bytes = 4
  key_bytes = 32
  mac_bytes = 16
  keystream key iv =
    let k' = from_le {n=4} <$> group 8 4 key
        i' = from_le {n=4} <$> group 3 4 iv
    in stream_concat $ map (\c => toList $ ChaCha.block 10 (cast c) k' i') $ drop 1 nats
  create_aad key iv aad ciphertext =
    let k' = from_le {n=4} <$> group 8 4 key
        i' = from_le {n=4} <$> group 3 4 iv
        s = le_to_integer $ take 32 $ ChaCha.block 10 0 k' i'
        r = clamp s
        length_aad = toList $ to_le {n=4} $ cast {to=Bits32} $ length aad
        length_ciphertext = toList $ to_le {n=4} $ cast {to=Bits32} $ length ciphertext
        ns = map (\x => le_to_integer' (x <+> [0x01])) $ chunk 16 (ciphertext ++ length_aad ++ length_ciphertext)
    in integer_to_le 16 (s + foldr (\n,a => mul_mod r (a + n) poly1305_prime) 0 ns)
-}
