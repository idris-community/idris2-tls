module Network.TLS.Signature

import Data.List
import Data.Vect
import Utils.Misc
import Utils.Bytes
import Utils.Parser
import Network.TLS.Parse.PEM
import Network.TLS.Parse.DER
import Network.TLS.Parsing
import Data.String.Parser
import Crypto.RSA
import Crypto.Curve
import Crypto.Curve.Weierstrass
import Crypto.Hash
import Crypto.Hash.OID

public export
data PublicKey : Type where
  RsaPublicKey : RSAPublicKey -> PublicKey
  EcdsaPublicKey : Point p => p -> PublicKey

public export
data SignatureParameter : Type where
  RSA_PKCSv15 : (DPair Type RegisteredHash) -> SignatureParameter
  RSA_PSS : (wit : DPair Type Hash) -> (salt_len : Nat) -> MaskGenerationFunction -> SignatureParameter
  ECDSA : DPair Type Hash -> SignatureParameter

export
Show PublicKey where
  show (RsaPublicKey _) = "RSA Public Key"
  show (EcdsaPublicKey _) = "ECDSA Public Key"

export
verify_signature : SignatureParameter -> PublicKey -> List Bits8 -> BitArray -> Either String ()
verify_signature (RSA_PKCSv15 hash_wit) (RsaPublicKey public_key) message (MkBitArray 0 signature) =
  if rsassa_pkcs1_v15_verify @{hash_wit.snd} public_key message signature then pure () else Left "signature does not match message"
verify_signature (RSA_PSS hash_wit salt_len mgf) (RsaPublicKey public_key) message (MkBitArray 0 signature) =
  if rsassa_pss_verify' @{hash_wit.snd} mgf salt_len public_key message signature then pure () else Left "signature does not match message"
verify_signature (ECDSA hash_wit) (EcdsaPublicKey public_key) message (MkBitArray 0 signature) = do
  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z signature) parse_asn1
  | (Pure leftover _) => Left "parser overfed for ecdsa signature"
  | (Fail err) => Left $ "parser error for ecdsasignature: " <+> show err
  | _ => Left "parser underfed for ecdsa signature"
  let (Universal ** 16 ** Sequence [ (Universal ** 2 ** IntVal x), (Universal ** 2 ** IntVal y) ] ) = ok
  | _ => Left "malformed ecdsa signature"
  let digest = hash @{hash_wit.snd} hash_wit.fst message
  if ecdsa_verify (be_to_integer digest) (MkSignature public_key (x, y)) then pure () else Left "signature does not match message"

verify_signature _ _ message signature = Left "public key does not match signature scheme"

export
extract_algorithm : ASN1Token -> Maybe (List Nat, Maybe ASN1Token)
extract_algorithm (Universal ** 16 ** Sequence [(Universal ** 6 ** OID algorithm)]) = Just (algorithm, Nothing)
extract_algorithm (Universal ** 16 ** Sequence ((Universal ** 6 ** OID algorithm) :: parameter :: [])) = Just (algorithm, Just parameter)
extract_algorithm _ = Nothing

export
oid_to_hash_algorithm : List Nat -> Maybe (DPair Type Hash)
oid_to_hash_algorithm oid =
  case map natToInteger oid of 
    [ 1, 3, 14, 3, 2, 26 ] => Just (MkDPair Sha1 %search)
    [ 2, 16, 840, 1, 101, 3, 4, 2, 1 ] => Just (MkDPair Sha256 %search)
    [ 2, 16, 840, 1, 101, 3, 4, 2, 2 ] => Just (MkDPair Sha384 %search)
    [ 2, 16, 840, 1, 101, 3, 4, 2, 3 ] => Just (MkDPair Sha512 %search)
    _ => Nothing

export
extract_signature_parameter : List Nat -> Maybe ASN1Token -> Either String SignatureParameter
extract_signature_parameter oid parameter = do
  case (map natToInteger oid, parameter) of
    ([1, 2, 840, 113549, 1, 1, 5], Just (Universal ** 5 ** Null)) =>  Right (RSA_PKCSv15 $ MkDPair Sha1 %search)
    ([1, 2, 840, 113549, 1, 1, 11], Just (Universal ** 5 ** Null)) => Right (RSA_PKCSv15 $ MkDPair Sha256 %search)
    ([1, 2, 840, 113549, 1, 1, 12], Just (Universal ** 5 ** Null)) => Right (RSA_PKCSv15 $ MkDPair Sha384 %search)
    ([1, 2, 840, 113549, 1, 1, 13], Just (Universal ** 5 ** Null)) => Right (RSA_PKCSv15 $ MkDPair Sha512 %search)
    ([1, 2, 840, 10045, 4, 3, 2], Nothing) => Right (ECDSA $ MkDPair Sha256 %search) 
    ([1, 2, 840, 10045, 4, 3, 3], Nothing) => Right (ECDSA $ MkDPair Sha384 %search) 
    ([1, 2, 840, 10045, 4, 3, 4], Nothing) => Right (ECDSA $ MkDPair Sha512 %search) 
    ([1, 2, 840, 113549, 1, 1, 10], Just (Universal ** 16 ** Sequence params)) => do
      (wit, params) <- extract_hash_algo params
      (mgf, params) <- extract_mgf params
      (salt, params) <- extract_salt_len params
      extract_trailer params
      pure $ RSA_PSS wit salt mgf
    _ => Left "unrecognized signature parameter"
  where
    extract_hash_algo' : ASN1Token -> Either String (DPair Type Hash)
    extract_hash_algo' (Universal ** 16 ** Sequence ((Universal ** 6 ** OID oid) :: _)) =
      maybe_to_either (oid_to_hash_algorithm oid) "hash algorithm not recognized"
    extract_hash_algo' _ = Left "malformed hash algorithm"

    extract_hash_algo : List ASN1Token -> Either String (DPair Type Hash, List ASN1Token)
    extract_hash_algo [] = Right (MkDPair Sha1 %search, [])
    extract_hash_algo ((ContextSpecific ** 0 ** UnknownConstructed _ _ [ hash_algo ] ) :: xs) =
      (, xs) <$> extract_hash_algo' hash_algo
    extract_hash_algo (x :: xs) = Right (MkDPair Sha1 %search, x :: xs)

    extract_mgf : List ASN1Token -> Either String (MaskGenerationFunction, List ASN1Token)
    extract_mgf [] = Right (mgf1 {algo=Sha1}, [])
    extract_mgf ((ContextSpecific ** 1 ** UnknownConstructed _ _ [ sequence ]) :: xs) =
      case sequence of
        ((Universal ** 16 ** Sequence ((Universal ** 6 ** OID oid) :: param :: []))) =>
          case map natToInteger oid of
            [ 1, 2, 840, 113549, 1, 1, 8 ] => (\wit => (mgf1 @{wit.snd}, xs)) <$> extract_hash_algo' param
            _ => Left "mask generation function not recognized"
        _ => Left "malformed mask generation function"
    extract_mgf (x :: xs) = Right (mgf1 {algo=Sha1}, x :: xs)

    extract_salt_len : List ASN1Token -> Either String (Nat, List ASN1Token)
    extract_salt_len [] = Right (20, [])
    extract_salt_len ((ContextSpecific ** 2 ** UnknownConstructed _ _ [ (Universal ** 2 ** IntVal salt_len) ]) :: xs) =
      if salt_len < 0 then Left "negative salt len" else pure (integerToNat salt_len, xs)
    extract_salt_len (x :: xs) = Right (20, x :: xs)

    extract_trailer : List ASN1Token -> Either String ()
    extract_trailer [] = Right ()
    extract_trailer [ (ContextSpecific ** 3 ** UnknownConstructed _ _ [ (Universal ** 2 ** IntVal trailer ) ]) ] =
      if trailer /= 1 then Left "invalid trailer field" else pure ()
    extract_trailer (x :: xs) = Left "unrecognized field after trailer field"

extract_rsa_key : List Bits8 -> Either String RSAPublicKey
extract_rsa_key pk_content = do
  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z pk_content) parse_asn1
  | (Pure leftover _) => Left "parser overfed for SubjectPublicKey"
  | (Fail err) => Left $ "parser error for SubjectPublicKey: " <+> show err
  | _ => Left "parser underfed for SubjectPublicKey"
  let (Universal ** 16 ** Sequence
        [ (Universal ** 2 ** IntVal modulus)
        , (Universal ** 2 ** IntVal public_exponent)
        ]
      ) = ok
  | _ => Left "cannot parse SubjectPublicKey"

  maybe_to_either (mk_rsa_publickey modulus public_exponent) "malformed RSA public key"

extract_ecdsa_key : List Bits8 -> List Integer -> Either String PublicKey
extract_ecdsa_key content [1, 2, 840, 10045, 3, 1, 7] =
  EcdsaPublicKey <$> maybe_to_either (decode {p=P256} content) "fail to parse secp256r1 public key"
extract_ecdsa_key content [1, 3, 132, 0, 34] =
  EcdsaPublicKey <$> maybe_to_either (decode {p=P384} content) "fail to parse secp384r1 public key"
extract_ecdsa_key content [1, 3, 132, 0, 35] =
  EcdsaPublicKey <$> maybe_to_either (decode {p=P521} content) "fail to parse secp521r1 public key"
extract_ecdsa_key _ oid = Left $ "unrecognized elliptic curve group oid: " <+> show oid

export
extract_key' : ASN1Token -> Either String (Vect 20 Bits8, PublicKey)
extract_key' ok = do
  let (Universal ** 16 ** Sequence 
        [ algorithm
        , (Universal ** 3 ** Bitstring bitstring)
        ]
      ) = ok
  | _ => Left "cannot parse SubjectPublicKeyInfo"

  let (MkBitArray 0 content) = bitstring
  | _ => Left "incorrect padding for SubjectPublicKey"

  key_info <- maybe_to_either (extract_algorithm algorithm) "cannot parse algorithm in SubjectPublicKeyInfo"

  -- natToInteger is needed because pattern matching list of Nat will kill my cpu big time
  public_key <- case mapFst (map natToInteger) key_info of 
    -- PKCS #1 RSA Encryption
    ([1, 2, 840, 113549, 1, 1, 1], Just (Universal ** 5 ** Null)) =>
      RsaPublicKey <$> extract_rsa_key content
    -- RSA PSS
    ([1, 2, 840, 113549, 1, 1, 10], Nothing) =>
      RsaPublicKey <$> extract_rsa_key content
    -- Elliptic Curve Public Key (RFC 5480)
    ([1, 2, 840, 10045, 2, 1], Just (Universal ** 6 ** OID group_id)) =>
      extract_ecdsa_key content $ map natToInteger group_id
    _ => Left "unrecognized signature algorithm parameter"

  pure (hash Sha1 content, public_key)

export
extract_key : List Bits8 -> Either String (Vect 20 Bits8, PublicKey)
extract_key der_public_key = do
  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z der_public_key) parse_asn1
  | (Pure leftover _) => Left "parser overfed for SubjectPublicKeyInfo"
  | (Fail err) => Left $ "parser error for SubjectPublicKeyInfo: " <+> show err
  | _ => Left "parser underfed for SubjectPublicKeyInfo"
  extract_key' ok
