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

public export
generate_key_pair : MonadRandom m => Nat -> m (PublicKey, SecretKey)
generate_key_pair k = do
  let e = 65537
  p <- generate_prime_part e (k `div` 2)
  q <- generate_prime_part e (minus k (k `div` 2))
  pure $ generate_key_pair_with_e p q e

public export
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

public export
rsa_decrypt_blinded : MonadRandom m => SecretKey -> Integer -> m Integer
rsa_decrypt_blinded k@(MkSecretKey n e d) c = do
  r <- generate_blinder n
  pure $ rsa_decrypt_blinded' k r c

public export
rsa_unsafe_decrypt : SecretKey -> Integer -> Integer
rsa_unsafe_decrypt = rsa_decrypt'

public export
rsa_sign : SecretKey -> Integer -> Integer
rsa_sign (MkSecretKey n e d) m = pow_mod m d n

public export
rsa_sign_extract_hash : PublicKey -> Integer -> Integer
rsa_sign_extract_hash (MkPublicKey n e) s = pow_mod s e n

public export
os2ip : Foldable t => t Bits8 -> Integer
os2ip = be_to_integer

public export
i2osp : Nat -> Integer -> Maybe (List Bits8)
i2osp b_len x =
  let mask = (shiftL 1 (8 * b_len)) - 1
      x' = x .&. mask
  in (guard $ x == x') $> (toList $ integer_to_be b_len x)

public export
rsavp1 : PublicKey -> Integer -> Maybe Integer
rsavp1 pk@(MkPublicKey n e) s = guard (s > 0 && s < (n - 1)) $> rsa_encrypt pk s

public export
emsa_pss_verify : {algo : _} -> Hash algo => Nat -> List Bits8 -> List Bits8 -> Nat -> Maybe ()
emsa_pss_verify sLen mHash em emBits = do
  let emLen = divCeilNZ emBits 8 SIsNonZero
  let hLen = digest_nbyte {algo=algo}
  -- 3. If emLen < hLen + sLen + 2, output "inconsistent" and stop.
  guard (emLen >= hLen + sLen + 2)
  -- 4. If the rightmost octet of EM does not have hexadecimal value 0xbc, output "inconsistent" and stop.
  fromList em >>= (\x => guard $ last x == the Bits8 0xbc)
  -- 5. Let maskedDB be the leftmost emLen - hLen - 1 octets of EM, and let H be the next hLen octets.
  let maskedDBLen = pred $ minus emLen hLen
  let (maskedDB@(x :: _), h) = splitAt maskedDBLen em
  | _ => Nothing
  -- 6. If the leftmost 8emLen - emBits bits of the leftmost octet in maskedDB are not all equal to zero, output "inconsistent" and stop.
  let h = take hLen h
  let emMaskL  = minus 8 (minus (emLen * 8) emBits)
  guard $ 0 == shiftR' x emMaskL
  -- 7. Let dbMask = MGF(H, emLen - hLen - 1).
  let dbMask = ?mgf h maskedDBLen
  -- 8. Let DB = maskedDB \xor dbMask.
  let (db' :: dbs) = zipWith xor dbMask maskedDB
  | _ => Nothing
  -- 9. Set the leftmost 8emLen - emBits bits of the leftmost octet in DB to zero.
  let db = (db' .&. (shiftR' (oneBits {a=Bits8}) emMaskL)) :: dbs
  pure ()
