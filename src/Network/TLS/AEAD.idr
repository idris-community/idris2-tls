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

aes_pad_iv_block : Vect 12 Bits8 -> Stream (Vect 16 Bits8)
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

keystream : Vect 16 Bits8 -> Vect 12 Bits8 -> Stream Bits8
keystream key iv =
  let key' = group 4 4 key
  in stream_concat $ map (toList . Vect.concat . encrypt_block AES128 key' . group 4 4) (aes_pad_iv_block iv)

create_aad : Vect 16 Bits8 -> Vect 12 Bits8 -> (aad : List Bits8) -> List Bits8 -> Vect 16 Bits8
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

public export
encrypt_aes_128_gcm : Vect 16 Bits8 -> Vect 12 Bits8 -> List Bits8 -> List Bits8 -> (List Bits8, Vect 16 Bits8)
encrypt_aes_128_gcm key iv plaintext aad =
  let ciphertext = zipWith xor plaintext (toList $ Stream.take (length plaintext) $ keystream key iv)
      mac_tag = create_aad key iv aad ciphertext
  in (ciphertext, mac_tag)

public export
decrypt_aes_128_gcm : Vect 16 Bits8 -> Vect 12 Bits8 -> List Bits8 -> List Bits8 -> List Bits8 -> (List Bits8, Bool)
decrypt_aes_128_gcm key iv ciphertext aad mac_tag' =
  let plaintext = zipWith xor ciphertext (toList $ Stream.take (length ciphertext) $ keystream key iv)
      mac_tag = create_aad key iv aad ciphertext
  in (plaintext, s_eq' (toList mac_tag) mac_tag')
