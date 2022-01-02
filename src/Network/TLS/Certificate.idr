module Network.TLS.Certificate

import Network.TLS.Parse.DER
import Network.TLS.Parse.PEM
import Network.TLS.Parsing
import Network.TLS.Signature
import Utils.Misc
import Utils.Bytes
import Utils.IPAddr
import Data.List
import Data.Vect
import Data.Bits
import Data.String.Parser
import Data.String.Extra
import Crypto.Hash

public export
data AttributeType : Type where
  CommonName : AttributeType
  Organization : AttributeType
  OrganizationUnit : AttributeType
  Country : AttributeType
  StateOrProvince : AttributeType
  LocalityName : AttributeType
  SerialNumber : AttributeType
  UnknownAttr : List Nat -> AttributeType

public export
Eq AttributeType where
  CommonName       == CommonName       = True
  Organization     == Organization     = True
  OrganizationUnit == OrganizationUnit = True
  Country          == Country          = True
  StateOrProvince  == StateOrProvince  = True
  LocalityName     == LocalityName     = True
  SerialNumber     == SerialNumber     = True
  UnknownAttr x    == UnknownAttr y        = x == y
  _ == _ = False

public export
Show AttributeType where
  show CommonName       = "CN"
  show Organization     = "O"
  show OrganizationUnit = "OU"
  show Country          = "C"
  show StateOrProvince  = "ST"
  show LocalityName     = "L"
  show SerialNumber     = "SERIALNUMBER"
  show (UnknownAttr x)  = show x

export
from_oid_attr : List Nat -> AttributeType
from_oid_attr oid =
  case map natToInteger oid of
    [ 2, 5, 4, 3 ]  => CommonName
    [ 2, 5, 4, 10 ] => Organization
    [ 2, 5, 4, 11 ] => OrganizationUnit
    [ 2, 5, 4, 6 ]  => Country
    [ 2, 5, 4, 8 ]  => StateOrProvince
    [ 2, 5, 4, 7 ]  => LocalityName
    [ 2, 5, 4, 5 ]  => SerialNumber 
    _ => UnknownAttr oid

public export
record RelativeDistinguishedName where
  constructor MkRDN
  attributes : List (AttributeType, String)

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
dn_attributes : DistinguishedName -> List (AttributeType, String)
dn_attributes dn = dn.rdns >>= attributes

public export
Show DistinguishedName where
  show dn = join "," $ go <$> dn_attributes dn
    where
      go : (AttributeType, String) -> String
      go (attribute, content) = show attribute <+> "=" <+> content

extract_attr : ASN1Token -> Maybe (AttributeType, String)
extract_attr (Universal ** 16 ** Sequence [ (Universal ** 6 ** OID oid), string ]) = (from_oid_attr oid,) <$> extract_string string
extract_attr _ = Nothing

extract_rdn : ASN1Token -> Maybe RelativeDistinguishedName
extract_rdn (Universal ** 17 ** Set attributes) = MkRDN <$> traverse extract_attr attributes
extract_rdn _ = Nothing

extract_dn : ASN1Token -> Maybe DistinguishedName
extract_dn (Universal ** 16 ** Sequence rdns) = MkDN <$> traverse extract_rdn rdns
extract_dn _ = Nothing

public export
data ExtensionType : Type where
  BasicConstraint : ExtensionType
  KeyUsage : ExtensionType
  SubjectAltName : ExtensionType
  UnknownExt : List Nat -> ExtensionType

public export
Show ExtensionType where
  show BasicConstraint        = "BasicConstraint"
  show KeyUsage               = "KeyUsage"
  show SubjectAltName         = "SubjectAltName"
  show (UnknownExt x)         = "UnknownExt (" <+> show x <+> ")"

from_oid_ext : List Nat -> ExtensionType
from_oid_ext oid =
  case map natToInteger oid of
    [ 2, 5, 29, 15 ] => KeyUsage
    [ 2, 5, 29, 19 ] => BasicConstraint
    [ 2, 5, 29, 17 ] => SubjectAltName
    _ => UnknownExt oid

public export
record ExtBasicConstraint where
  constructor MkExtBasicConstraint
  ca : Bool
  path_len : Maybe Nat

public export
record ExtKeyUsage where
  constructor MkExtKeyUsage
  digital_signature : Bool
  non_repudiation   : Bool
  key_encipherment  : Bool
  data_encipherment : Bool
  key_agreement     : Bool
  key_cert_sign     : Bool
  crl_sign          : Bool
  encipher_only     : Bool
  decipher_only     : Bool

public export
data GeneralName : Type where
  DNSName : String -> GeneralName
  IPv4Addr : IPv4Addr -> GeneralName
  IPv6Addr : IPv6Addr -> GeneralName
  UnknownGN : ASN1Token -> GeneralName

public export
Show GeneralName where
  show (DNSName dns_name) = "DNS: " <+> dns_name
  show (IPv4Addr addr) = "IP Address: " <+> show addr
  show (IPv6Addr addr) = "IP Address: " <+> show addr
  show (UnknownGN _) = "<unknown>"

extract_general_name : ASN1Token -> Either String GeneralName
extract_general_name (ContextSpecific ** 2 ** UnknownPrimitive _ _ str) = Right $ DNSName $ ascii_to_string str
extract_general_name (ContextSpecific ** 7 ** UnknownPrimitive _ _ str) =
  let vec = fromList str
      gn = (IPv4Addr . MkIPv4Addr <$> exactLength 4 vec) <|> (IPv6Addr . MkIPv6Addr <$> exactLength 16 vec)
  in maybe_to_either gn "invalid IP address"
extract_general_name x = Right $ UnknownGN x

public export
record ExtSubjectAltName where
  constructor MkExtSubjectAltName
  general_names : List GeneralName

public export
extension_type : ExtensionType -> Type
extension_type BasicConstraint = ExtBasicConstraint
extension_type KeyUsage = ExtKeyUsage
extension_type SubjectAltName = ExtSubjectAltName
extension_type _ = List Bits8

parse_to_extension_type : (t : ExtensionType) -> List Bits8 -> Either String (extension_type t)
parse_to_extension_type BasicConstraint body = do
  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z body) parse_asn1
  | (Pure leftover _) => Left $ "malformed basic constraint ext: leftover: " <+> (xxd $ map get leftover)
  | (Fail err) => Left $ show err
  | _ => Left "malformed basic constraint: underfed"
  let ( Universal ** 16 ** Sequence content ) = ok
  | _ => Left "malformed basic constraint: structure error"
  case content of
    [] =>
      Right (MkExtBasicConstraint False Nothing)
    [ (Universal ** 1 ** Boolean ca) ] =>
      Right (MkExtBasicConstraint ca Nothing)
    [ (Universal ** 1 ** Boolean ca), (Universal ** 2 ** IntVal depth) ] =>
      Right (MkExtBasicConstraint ca $ Just $ integerToNat depth)
    _ =>
      Left "malformed basic constraint: structure error"
parse_to_extension_type KeyUsage body = do
  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z body) parse_asn1
  | (Pure leftover _) => Left $ "malformed key usage ext: leftover: " <+> (xxd $ map get leftover)
  | (Fail err) => Left $ show err
  | _ => Left "malformed key usage: underfed"
  let (Universal ** 3 ** Bitstring content) = ok
  | _ => Left "malformed key usage: structure error"
  case take 9 ((content.bytes >>= (toList . to_bools_be)) <+> replicate 9 False) of
    [a, b, c, d, e, f, g, h, i] => Right $ MkExtKeyUsage a b c d e f g h i
    _ => Left "impossible"
parse_to_extension_type SubjectAltName body = do
  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z body) parse_asn1
  | (Pure leftover _) => Left $ "malformed subject alt name ext: leftover: " <+> (xxd $ map get leftover)
  | (Fail err) => Left $ show err
  | _ => Left "malformed subject alt name: underfed"
  let (Universal ** 16 ** Sequence content) = ok
  | _ => Left "malformed subject alt name: structure error"
  MkExtSubjectAltName <$> traverse extract_general_name content
parse_to_extension_type (UnknownExt x) body = Right body

public export
record Extension where
  constructor MkExt
  extension_id : ExtensionType
  critical : Bool
  value : extension_type extension_id

extract_extension : ASN1Token -> Either String Extension
extract_extension (Universal ** 16 ** Sequence
                  [ (Universal ** 6 ** OID oid)
                  , (Universal ** 1 ** Boolean critical)
                  , (Universal ** 4 ** OctetString value)
                  ]) = let ext_id = from_oid_ext oid in (MkExt ext_id critical) <$> parse_to_extension_type ext_id value
extract_extension (Universal ** 16 ** Sequence
                  [ (Universal ** 6 ** OID oid)
                  , (Universal ** 4 ** OctetString value)
                  ]) = let ext_id = from_oid_ext oid in (MkExt ext_id False) <$> parse_to_extension_type ext_id value
extract_extension _ = Left "malformed extension field"

extract_extensions : List ASN1Token -> Either String (List Extension)
extract_extensions [] = Right []
extract_extensions (x :: xs) =
  case last (x :: xs) of
    (ContextSpecific ** 3 ** UnknownConstructed _ _ [ (Universal ** 16 ** Sequence extensions) ]) => traverse extract_extension extensions
    _ => Left "malformed extension list field"

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
  cert_public_key_id : Vect 20 Bits8
  sig_algorithm : (List Nat, List ASN1Token)
  signature_value : BitArray
  extensions : List Extension
  raw_bytes : List Bits8

public export
Show Certificate where
  show cert = "Subject: " <+> show cert.subject <+> " Issuer: " <+> show cert.issuer

export
certificate_subject_names : Certificate -> List GeneralName
certificate_subject_names cert = go (toList (DNSName <$> common_name)) cert.extensions
  where
    go : List GeneralName -> List Extension -> List GeneralName
    go acc [] = acc
    go acc (x :: xs) =
      case x of
        MkExt SubjectAltName _ ext => go (acc <+> ext.general_names) xs
        _ => go acc xs
    common_name : Maybe String
    common_name = lookup CommonName $ dn_attributes cert.subject

export
is_self_signed : Certificate -> Bool
is_self_signed cert = cert.issuer == cert.subject

export
extract_key_usage : Certificate -> Maybe ExtKeyUsage
extract_key_usage cert = go cert.extensions
  where
    go : List Extension -> Maybe ExtKeyUsage
    go (MkExt KeyUsage _ ext :: xs) = Just ext
    go (x :: xs) = go xs
    go [] = Nothing

export
extract_basic_constraint : Certificate -> Maybe ExtBasicConstraint
extract_basic_constraint cert = go cert.extensions
  where
    go : List Extension -> Maybe ExtBasicConstraint
    go (MkExt BasicConstraint _ ext :: xs) = Just ext
    go (x :: xs) = go xs
    go [] = Nothing

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

  (key_id, key) <- extract_key' certificate_public_key

  crt_algorithm <- maybe_to_either (extract_algorithm crt_algorithm) "malformed certificate algorithm"
  crt_signature_algorithm <- maybe_to_either (extract_algorithm crt_signature_algorithm) "malformed certificate signature algorithm"

  issuer <- maybe_to_either (extract_dn issuer) "malformed issuer"
  subject <- maybe_to_either (extract_dn subject) "malformed subject"

  extensions <- extract_extensions optional_fields

  pure $
    MkCertificate
      serial_number
      crt_algorithm
      issuer
      valid_not_before
      valid_not_after
      subject
      key
      key_id
      crt_signature_algorithm
      signature_value
      extensions
      blob
