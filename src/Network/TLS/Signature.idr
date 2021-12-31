module Network.TLS.Signature

import Data.List
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
import Crypto.Hash.SHA2
import Crypto.Hash.OID

public export
data PublicKey : Type where
  RsaPssRsaePublicKey : RSAPublicKey -> PublicKey
  RsaPkcs15PublicKey : DPair Type RegisteredHash -> RSAPublicKey -> PublicKey
  EcdsaPublicKey : Point p => p -> PublicKey

export
Show PublicKey where
  show (RsaPssRsaePublicKey _) = "RSA PSS RSAE Key"
  show (RsaPkcs15PublicKey _ _) = "RSA PKCS v1.5 Key"
  show (EcdsaPublicKey _) = "ECDSA Key"

export
extract_algorithm : ASN1Token -> Maybe (List Nat, (List (t ** n ** ASN1 t n)))
extract_algorithm (Universal ** 16 ** Sequence ((Universal ** 6 ** OID algorithm) :: parameter)) = Just (algorithm, parameter)
extract_algorithm _ = Nothing

extract_rsa_key : BitArray -> Either String RSAPublicKey
extract_rsa_key content = do
  let (MkBitArray 0 pk_content) = content
  | _ => Left "incorrect padding for SubjectPublicKey"

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

extract_ecdsa_key : BitArray -> List Integer -> Either String PublicKey
extract_ecdsa_key (MkBitArray 0 content) [1, 2, 840, 10045, 3, 1, 7] =
  EcdsaPublicKey <$> maybe_to_either (decode {p=P256} content) "fail to parse secp256r1 public key"
extract_ecdsa_key (MkBitArray 0 content) [1, 3, 132, 0, 34] =
  EcdsaPublicKey <$> maybe_to_either (decode {p=P384} content) "fail to parse secp384r1 public key"
extract_ecdsa_key (MkBitArray 0 content) [1, 3, 132, 0, 35] =
  EcdsaPublicKey <$> maybe_to_either (decode {p=P521} content) "fail to parse secp521r1 public key"
extract_ecdsa_key _ oid = Left $ "unrecognized elliptic curve group oid: " <+> show oid

export
extract_key' : ASN1Token -> Either String PublicKey
extract_key' ok = do
  let (Universal ** 16 ** Sequence 
        [ algorithm
        , (Universal ** 3 ** Bitstring content)
        ]
      ) = ok
  | _ => Left "cannot parse SubjectPublicKeyInfo"

  key_info <- maybe_to_either (extract_algorithm algorithm) "cannot parse algorithm in SubjectPublicKeyInfo"

  -- natToInteger is needed because pattern matching list of Nat will kill my cpu big time
  case mapFst (map natToInteger) key_info of 
    -- PKCS #1 RSA Encryption
    ([1, 2, 840, 113549, 1, 1, 1], [(Universal ** 5 ** Null)]) =>
      RsaPssRsaePublicKey <$> extract_rsa_key content
    -- sha256WithRSAEncryption
    ([1, 2, 840, 113549, 1, 1, 11], [(Universal ** 5 ** Null)]) =>
      RsaPkcs15PublicKey (MkDPair Sha256 %search) <$> extract_rsa_key content
    -- sha384WithRSAEncryption
    ([1, 2, 840, 113549, 1, 1, 12], [(Universal ** 5 ** Null)]) =>
      RsaPkcs15PublicKey (MkDPair Sha384 %search) <$> extract_rsa_key content
    -- sha512WithRSAEncryption
    ([1, 2, 840, 113549, 1, 1, 13], [(Universal ** 5 ** Null)]) =>
      RsaPkcs15PublicKey (MkDPair Sha512 %search) <$> extract_rsa_key content
    -- Elliptic Curve Public Key (RFC 5480)
    ([1, 2, 840, 10045, 2, 1], [(Universal ** 6 ** OID group_id)]) =>
      extract_ecdsa_key content $ map natToInteger group_id
    _ => Left "unrecognized signature algorithm parameter"

export
extract_key : List Bits8 -> Either String PublicKey
extract_key der_public_key = do
  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z der_public_key) parse_asn1
  | (Pure leftover _) => Left "parser overfed for SubjectPublicKeyInfo"
  | (Fail err) => Left $ "parser error for SubjectPublicKeyInfo: " <+> show err
  | _ => Left "parser underfed for SubjectPublicKeyInfo"
  extract_key' ok

