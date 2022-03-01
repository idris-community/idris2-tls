module Crypto.RSA

import Data.List
import Data.Vect
import Data.Bits
import Utils.Misc
import Utils.Bytes
import Crypto.Random
import Data.Nat
import Crypto.Hash
import Data.List1
import Data.Fin
import Data.Stream
import Data.Fin.Extra
import Crypto.Hash.OID

export
data RSAPublicKey : Type where
  MkRSAPublicKey : (n : Integer) -> (e : Integer) -> RSAPublicKey

-- TODO: check if there are more constraints needed between n and e
-- also maybe use a proof instead of masking the constructor in the future
export
mk_rsa_publickey : Integer -> Integer -> Maybe RSAPublicKey
mk_rsa_publickey n e = guard (1 == gcd' n e) $> MkRSAPublicKey n e

export
rsa_encrypt : RSAPublicKey -> Integer -> Integer
rsa_encrypt (MkRSAPublicKey n e) m = pow_mod m e n

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
rsavp1 : RSAPublicKey -> Integer -> Maybe Integer
rsavp1 pk@(MkRSAPublicKey n e) s = guard (s > 0 && s < (n - 1)) $> rsa_encrypt pk s

record PSSEncodedMessage n where
  hash_digest : Vect n Bits8
  db : List Bits8

public export
MaskGenerationFunction : Type
MaskGenerationFunction = (n : Nat) -> List Bits8 -> Vect n Bits8

export
mgf1 : {algo : _} -> (h : Hash algo) => MaskGenerationFunction
mgf1 n seed = take n $ stream_concat $ map (\x => hash algo (seed <+> (toList $ integer_to_be 4 $ cast x))) nats

export
modulus_bits : RSAPublicKey -> Nat
modulus_bits (MkRSAPublicKey n _) = if n > 0 then go Z n else 0
  where
    go : Nat -> Integer -> Nat
    go n x = if x == 0 then n else go (S n) (shiftR x 1)

export
emsa_pss_verify : {algo : _} -> (h : Hash algo) => MaskGenerationFunction -> Nat -> List Bits8 -> List1 Bits8 -> Nat -> Maybe ()
emsa_pss_verify mgf sLen message em emBits = do
  let mHash = hash algo message
  let emLen = divCeilNZ emBits 8 SIsNonZero
  let (em, 0xbc) = uncons1 em
  | _ => Nothing -- Invalid padding
  (maskedDB, digest) <- splitLastAt1 (digest_nbyte {algo}) em
  -- check padding
  guard $ check_padding (modFinNZ emBits 8 SIsNonZero) (head maskedDB)
  let db = zipWith xor (toList maskedDB) (toList $ mgf (length maskedDB) (toList digest))
  (padding, salt) <- splitLastAt1 sLen db
  -- unset padding bits
  bits_to_be_cleared <- natToFin (minus (8 * emLen) emBits) _
  let mask = shiftR (the Bits8 oneBits) bits_to_be_cleared
  let (pxs, px) = uncons1 $ (mask .&. head padding) ::: (tail padding)
  -- check padding
  guard (0 == (foldr (.|.) 0 pxs))
  guard (1 == px)
  -- check salt length
  guard $ digest `s_eq` hash algo (replicate 8 0 <+> toList mHash <+> toList salt)
  where
    check_padding : Fin 8 -> Bits8 -> Bool
    check_padding FZ _ = True
    check_padding n b = 0 == shiftR b n

export
rsassa_pss_verify' : {algo : _} -> (h : Hash algo) => MaskGenerationFunction -> Nat -> RSAPublicKey -> List Bits8 -> List Bits8 -> Bool
rsassa_pss_verify' mask_gen salt_len pk message signature = isJust $ do
  let modBits = modulus_bits pk
  let s = os2ip signature
  m <- rsavp1 pk s
  let emLen = divCeilNZ (pred modBits) 8 SIsNonZero
  em <- i2osp emLen m >>= fromList
  emsa_pss_verify {algo} mask_gen salt_len message em (pred modBits)

export
rsassa_pss_verify : {algo : _} -> Hash algo => RSAPublicKey -> List Bits8 -> List Bits8 -> Bool
rsassa_pss_verify = rsassa_pss_verify' {algo} (mgf1 {algo}) (digest_nbyte {algo})

export
emsa_pkcs1_v15_encode : {algo : _} -> RegisteredHash algo => List Bits8 -> Nat -> Maybe (List Bits8)
emsa_pkcs1_v15_encode message emLen = do
  let h = hashWithHeader {algo} message
  let paddingLen = (emLen `minus` der_digest_n_byte {algo}) `minus` 3
  guard (paddingLen >= 8)
  let padding = replicate paddingLen 0xff
  pure $ [ 0x00, 0x01 ] <+> padding <+> [ 0x00 ] <+> toList h

export
rsassa_pkcs1_v15_verify : {algo : _} -> RegisteredHash algo => RSAPublicKey -> List Bits8 -> List Bits8 -> Bool
rsassa_pkcs1_v15_verify pk message signature = isJust $ do
  let k = divCeilNZ (modulus_bits pk) 8 SIsNonZero
  guard (k == length signature)

  let s = os2ip signature
  m <- rsavp1 pk s
  em <- i2osp k m

  em' <- emsa_pkcs1_v15_encode {algo} message k
  guard (em `s_eq'` em')
