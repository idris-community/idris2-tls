module Crypto.RSA

import Data.List
import Data.Vect
import Data.Bits
import Utils.Misc
import Utils.Bytes
import Crypto.Prime
import Crypto.Random
import Data.Nat
import Crypto.Hash
import Data.List1
import Data.Fin
import Data.Stream
import Data.Fin.Extra
import Crypto.Hash.OID

data PublicKey : Type where
  MkPublicKey : (n : Integer) -> (e : Integer) -> PublicKey

data SecretKey : Type where
  MkSecretKey : (n : Integer) -> (e : Integer) -> (d : Integer) -> SecretKey

-- p q must be primes or the skinwalker will devour your offsprings
-- p = genprime(k/2) until p mod e /= 1
-- q = genprime(k-k/2) until q mod e /= 1
-- e and (p-1)(q-1) should be coprimes
generate_key_pair_with_e : Integer -> Integer -> Integer -> (PublicKey, SecretKey)
generate_key_pair_with_e p q e =
  let n = p * q
      d = inv_mul_mod e ((p-1)*(q-1))
  in (MkPublicKey n e, MkSecretKey n e d)

-- p q must be primes or the skinwalker will devour your offsprings
generate_key_pair' : Integer -> Integer -> (PublicKey, SecretKey)
generate_key_pair' p q = generate_key_pair_with_e p q 65537

generate_prime_part : MonadRandom m => Integer -> Nat -> m Integer
generate_prime_part e bits = do
  p <- generate_prime bits
  if (p `mod` e) == 1 then generate_prime_part e bits else pure p

export
generate_key_pair : MonadRandom m => Nat -> m (PublicKey, SecretKey)
generate_key_pair k = do
  let e = 65537
  p <- generate_prime_part e (k `div` 2)
  q <- generate_prime_part e (minus k (k `div` 2))
  pure $ generate_key_pair_with_e p q e

export
rsa_encrypt : PublicKey -> Integer -> Integer
rsa_encrypt (MkPublicKey n e) m = pow_mod m e n

-- r and n should be coprimes or you die
mask_on : SecretKey -> Integer -> Integer -> Integer
mask_on (MkSecretKey n e d) r x = pow_mod (x * r) e n

mask_off : SecretKey -> Integer -> Integer -> Integer
mask_off (MkSecretKey n e d) r z = pow_mod (mul_mod (inv_mul_mod r n) z n) d n

rsa_decrypt' : SecretKey -> Integer -> Integer
rsa_decrypt' (MkSecretKey n e d) c = pow_mod c d n

generate_blinder : MonadRandom m => Integer -> m Integer
generate_blinder n = do
  r <- uniform_random' 2 (n - 1)
  if are_coprimes r n then pure r else generate_blinder n

-- Timing attack resistant
rsa_decrypt_blinded' : SecretKey -> Integer -> Integer -> Integer
rsa_decrypt_blinded' k@(MkSecretKey n e d) r c = mask_off k r $ rsa_decrypt' k $ mask_on k r c

export
rsa_decrypt_blinded : MonadRandom m => SecretKey -> Integer -> m Integer
rsa_decrypt_blinded k@(MkSecretKey n e d) c = do
  r <- generate_blinder n
  pure $ rsa_decrypt_blinded' k r c

export
rsa_unsafe_decrypt : SecretKey -> Integer -> Integer
rsa_unsafe_decrypt = rsa_decrypt'

export
rsa_sign : SecretKey -> Integer -> Integer
rsa_sign (MkSecretKey n e d) m = pow_mod m d n

export
rsa_sign_extract_hash : PublicKey -> Integer -> Integer
rsa_sign_extract_hash (MkPublicKey n e) s = pow_mod s e n

-- RFC 8017

export
os2ip : Foldable t => t Bits8 -> Integer
os2ip = be_to_integer

export
i2osp : Nat -> Integer -> Maybe (List Bits8)
i2osp b_len x =
  let mask = (shiftL 1 (8 * b_len)) - 1
      x' = x .&. mask
  in (guard $ x == x') $> (toList $ integer_to_be b_len x)

export
rsavp1 : PublicKey -> Integer -> Maybe Integer
rsavp1 pk@(MkPublicKey n e) s = guard (s > 0 && s < (n - 1)) $> rsa_encrypt pk s

record PSSEncodedMessage n where
  hash_digest : Vect n Bits8
  db : List Bits8

mgf1 : {algo : _} -> Hash algo => (n : Nat) -> List Bits8 -> Vect n Bits8
mgf1 n seed = take n $ stream_concat $ map (\x => hash algo (seed <+> (toList $ integer_to_be 4 $ cast x))) nats

modulus_bits : PublicKey -> Nat
modulus_bits (MkPublicKey n _) = if n > 0 then go Z $ iterate (\y => shiftR y 1) n else 0
  where
    go : Nat -> Stream Integer -> Nat
    go n (x :: xs) = if x == 0 then n else go (S n) xs

emsa_pss_verify : {algo : _} -> Hash algo => Nat -> List Bits8 -> List1 Bits8 -> Nat -> Maybe ()
emsa_pss_verify sLen message em emBits = do
  let mHash = hash algo message
  let emLen = divCeilNZ emBits 8 SIsNonZero
  let (em, 0xbc) = uncons1 em
  | _ => Nothing -- Invalid padding
  (maskedDB, digest) <- splitLastAt1 (digest_nbyte {algo}) em
  -- check padding
  guard $ check_padding (modFinNZ emBits 8 SIsNonZero) (head maskedDB)
  let db = zipWith xor (toList maskedDB) (toList $ mgf1 {algo} (length maskedDB) (toList digest))
  (padding, salt) <- splitLastAt1 sLen db
  -- check padding
  guard (1 == be_to_integer padding)
  -- check salt length
  guard $ digest `s_eq` hash algo ([0, 0, 0, 0, 0, 0, 0, 0] <+> toList mHash <+> toList salt)
  where
    check_padding : Fin 8 -> Bits8 -> Bool
    check_padding FZ _ = True
    check_padding n b = 0 == shiftR b n

export
rsassa_pss_verify : {algo : _} -> Hash algo => PublicKey -> List Bits8 -> List Bits8 -> Bool
rsassa_pss_verify pk message signature = isJust $ do
  let modBits = modulus_bits pk
  let s = os2ip signature
  m <- rsavp1 pk s
  let emLen = divCeilNZ (pred modBits) 8 SIsNonZero
  em <- i2osp emLen m >>= fromList
  emsa_pss_verify {algo} (digest_nbyte {algo}) message em (pred modBits)

emsa_pkcs1_v15_encode : {algo : _} -> RegisteredHash algo => List Bits8 -> Nat -> Maybe (List Bits8)
emsa_pkcs1_v15_encode message emLen = do
  let h = hashWithHeader {algo} message
  let paddingLen = (emLen `minus` der_digest_n_byte {algo}) `minus` 3
  guard (paddingLen >= 8)
  let padding = replicate paddingLen 0xff
  pure $ [ 0x00, 0x01 ] <+> padding <+> [ 0x00 ] <+> toList h

export
rsassa_pkcs1_v15_verify : {algo : _} -> RegisteredHash algo => PublicKey -> List Bits8 -> List Bits8 -> Bool
rsassa_pkcs1_v15_verify pk message signature = isJust $ do
  let k = divCeilNZ (modulus_bits pk) 8 SIsNonZero
  guard (k == length signature)

  let s = os2ip signature
  m <- rsavp1 pk s
  em <- i2osp k m
  
  em' <- emsa_pkcs1_v15_encode {algo} message k
  guard (em `s_eq'` em')
