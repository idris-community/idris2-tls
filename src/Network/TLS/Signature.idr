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

public export
data PublicKey : Type where
  RSAPublicKey : RSAPublicKey -> PublicKey
  ECDSAPublicKey : Point p => p -> PublicKey

export
extract_algorithm : ASN1Token -> Maybe (List Nat, (List (t ** n ** ASN1 t n)))
extract_algorithm (Universal ** 16 ** Sequence ((Universal ** 6 ** OID algorithm) :: parameter)) = Just (algorithm, parameter)
extract_algorithm _ = Nothing

extract_rsa_key : BitArray -> Either String PublicKey
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

  RSAPublicKey <$> maybe_to_either (mk_rsa_publickey modulus public_exponent) "malformed RSA public key"

extract_ecdsa_key : BitArray -> List Integer -> Either String PublicKey
extract_ecdsa_key (MkBitArray 0 content) [1, 2, 840, 10045, 3, 1, 7] =
  ECDSAPublicKey <$> maybe_to_either (decode {p=P256} content) "fail to parse secp256r1 public key"
extract_ecdsa_key (MkBitArray 0 content) [1, 3, 132, 0, 34] =
  ECDSAPublicKey <$> maybe_to_either (decode {p=P384} content) "fail to parse secp384r1 public key"
extract_ecdsa_key (MkBitArray 0 content) [1, 3, 132, 0, 35] =
  ECDSAPublicKey <$> maybe_to_either (decode {p=P521} content) "fail to parse secp521r1 public key"
extract_ecdsa_key _ oid = Left $ "unrecognized elliptic curve group oid: " <+> show oid

export
extract_key : List Bits8 -> Either String PublicKey
extract_key der_public_key = do
  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z der_public_key) parse_asn1
  | (Pure leftover _) => Left "parser overfed for SubjectPublicKeyInfo"
  | (Fail err) => Left $ "parser error for SubjectPublicKeyInfo: " <+> show err
  | _ => Left "parser underfed for SubjectPublicKeyInfo"

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
      extract_rsa_key content
    -- Elliptic Curve Public Key (RFC 5480)
    ([1, 2, 840, 10045, 2, 1], [(Universal ** 6 ** OID group_id)]) =>
      extract_ecdsa_key content $ map natToInteger group_id
    _ => Left "unrecognized signature algorithm parameter"

