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

export
Show PublicKey where
  show (RsaPublicKey _) = "RSA Public Key"
  show (EcdsaPublicKey _) = "ECDSA Public Key"

export
extract_algorithm : ASN1Token -> Maybe (List Nat, Maybe ASN1Token)
extract_algorithm (Universal ** 16 ** Sequence [(Universal ** 6 ** OID algorithm)]) = Just (algorithm, Nothing)
extract_algorithm (Universal ** 16 ** Sequence ((Universal ** 6 ** OID algorithm) :: parameter :: [])) = Just (algorithm, Just parameter)
extract_algorithm _ = Nothing

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
