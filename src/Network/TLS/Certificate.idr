module Network.TLS.Certificate

import Network.TLS.Parse.DER
import Network.TLS.Parse.PEM
import Network.TLS.Parsing
import Network.TLS.Signature
import Utils.Misc
import Utils.Bytes
import Data.List
import Data.String.Parser

public export
record RelativeDistinguishedName where
  constructor MkRDN
  attributes : List (List Nat, String)

public export
record DistinguishedName where
  constructor MkDN
  rdns : List RelativeDistinguishedName

public export
Eq RelativeDistinguishedName where
  a == b = (length a.attributes == length b.attributes) && ((a.attributes \\ b.attributes) == [])

public export
Eq DistinguishedName where
  a == b = a.rdns == b.rdns

export
dn_attributes : DistinguishedName -> List (List Nat, String)
dn_attributes dn = dn.rdns >>= attributes

extract_attr : ASN1Token -> Maybe (List Nat, String)
extract_attr (Universal ** 16 ** Sequence [ (Universal ** 6 ** OID oid), string ]) = (oid,) <$> extract_string string
extract_attr _ = Nothing

extract_rdn : ASN1Token -> Maybe RelativeDistinguishedName
extract_rdn (Universal ** 17 ** Set attributes) = MkRDN <$> traverse extract_attr attributes
extract_rdn _ = Nothing

extract_dn : ASN1Token -> Maybe DistinguishedName
extract_dn (Universal ** 16 ** Sequence rdns) = MkDN <$> traverse extract_rdn rdns
extract_dn _ = Nothing

public export
record Certificate where
  constructor MkCertificate
  serial_number : Integer
  crt_algorithm : (List Nat, List ASN1Token)
  issuer : DistinguishedName
  valid_not_before : Integer
  valid_not_after : Integer
  subject : DistinguishedName
  cert_public_key : PublicKey
  sig_algorithm : (List Nat, List ASN1Token)
  signature_value : BitArray

export
parse_certificate : List Bits8 -> Either String Certificate
parse_certificate blob = do
  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z blob) parse_asn1
  | (Pure leftover _) => Left $ "malformed certificate: leftover: " <+> (xxd $ map get leftover)
  | (Fail err) => Left $ show err
  | _ => Left "malformed certificate: underfed"

  let (Universal ** 16 ** Sequence
        [ (Universal ** 16 ** Sequence
          ( (ContextSpecific ** 0 ** UnknownConstructed _ _ [ (Universal ** 2 ** IntVal 2) ])
          :: (Universal ** 2 ** IntVal serial_number)
          :: crt_algorithm
          :: issuer
          :: (Universal ** 16 ** Sequence valid_period)
          :: subject
          :: certificate_public_key
          :: optional_fields
          ))
        , crt_signature_algorithm
        , (Universal ** 3 ** Bitstring signature_value)
        ]
      ) = ok
  | _ => Left "malformed certificate"

  let Just [ valid_not_before, valid_not_after ] = traverse {f=Maybe} extract_epoch valid_period
  | _ => Left "malformed validity timestamp"
  
  key <- extract_key' certificate_public_key

  crt_algorithm <- maybe_to_either (extract_algorithm crt_algorithm) "malformed certificate algorithm"
  crt_signature_algorithm <- maybe_to_either (extract_algorithm crt_signature_algorithm) "malformed certificate signature algorithm"

  issuer <- maybe_to_either (extract_dn issuer) "malformed issuer"
  subject <- maybe_to_either (extract_dn subject) "malformed subject"

  pure $
    MkCertificate
      serial_number
      crt_algorithm
      issuer
      valid_not_before
      valid_not_after
      subject
      key
      crt_signature_algorithm
      signature_value
