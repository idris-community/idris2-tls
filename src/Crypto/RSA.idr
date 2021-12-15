module Crypto.RSA

import Data.List
import Data.Vect
import Data.Bits
import Utils.Misc
import Crypto.Random

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
