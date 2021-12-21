module Network.TLS.Magic

import Data.Vect
import Network.TLS.Parsing
import Network.TLS.AEAD
import Utils.Bytes
import Utils.Misc
import Crypto.Hash
import Crypto.ECDH
import Crypto.Curve
import Crypto.Curve.Weierstrass

-- in TLS 1.3, the severity is implicit in the type of alert being sent, and the "level" field can safely be ignored
public export
data AlertLevel : Type where
  Warning : AlertLevel
  Fatal : AlertLevel

public export
Show AlertLevel where
  show Warning = "Warning"
  show Fatal = "Fatal"

public export
alert_level_to_id : AlertLevel -> Bits8
alert_level_to_id Warning = 1
alert_level_to_id Fatal = 2

public export
id_to_alert_level : Bits8 -> Maybe AlertLevel
id_to_alert_level 1 = Just Warning
id_to_alert_level 2 = Just Warning
id_to_alert_level _ = Nothing

public export
data AlertDescription : Type where
  CloseNotify : AlertDescription
  UnexpectedMessage : AlertDescription
  BadRecordMac : AlertDescription
  RecordOverflow : AlertDescription
  HandshakeFailure : AlertDescription
  BadCertificate : AlertDescription
  UnsupportedCertificate : AlertDescription
  CertificateRevoked : AlertDescription
  CertificateExpired : AlertDescription
  CertificateUnknown : AlertDescription
  IllegalParameter : AlertDescription
  UnknownCA : AlertDescription
  AccessDenied : AlertDescription
  DecodeError : AlertDescription
  DecryptError : AlertDescription
  ProtocolVersion : AlertDescription
  InsufficientSecurity : AlertDescription
  InternalError : AlertDescription
  InappropriateFallback : AlertDescription
  UserCanceled : AlertDescription
  MissingExtension : AlertDescription
  UnsupportedExtension : AlertDescription
  UnrecognizedName : AlertDescription
  BadCertificateStatusResponse : AlertDescription
  UnknownPskIdentity : AlertDescription
  CertificateRequired : AlertDescription
  NoApplicationProtocol : AlertDescription

public export
Show AlertDescription where
  show CloseNotify = "CloseNotify"
  show UnexpectedMessage = "UnexpectedMessage"
  show BadRecordMac = "BadRecordMac"
  show RecordOverflow = "RecordOverflow"
  show HandshakeFailure = "HandshakeFailure"
  show BadCertificate = "BadCertificate"
  show UnsupportedCertificate = "UnsupportedCertificate"
  show CertificateRevoked = "CertificateRevoked"
  show CertificateExpired = "CertificateExpired"
  show CertificateUnknown = "CertificateUnknown"
  show IllegalParameter = "IllegalParameter"
  show UnknownCA = "UnknownCA"
  show AccessDenied = "AccessDenied"
  show DecodeError = "DecodeError"
  show DecryptError = "DecryptError"
  show ProtocolVersion = "ProtocolVersion"
  show InsufficientSecurity = "InsufficientSecurity"
  show InternalError = "InternalError"
  show InappropriateFallback = "InappropriateFallback"
  show UserCanceled = "UserCanceled"
  show MissingExtension = "MissingExtension"
  show UnsupportedExtension = "UnsupportedExtension"
  show UnrecognizedName = "UnrecognizedName"
  show BadCertificateStatusResponse = "BadCertificateStatusResponse"
  show UnknownPskIdentity = "UnknownPskIdentity"
  show CertificateRequired = "CertificateRequired"
  show NoApplicationProtocol = "NoApplicationProtocol"

public export
alert_description_to_id : AlertDescription -> Bits8
alert_description_to_id CloseNotify = 0
alert_description_to_id UnexpectedMessage = 10
alert_description_to_id BadRecordMac = 20
alert_description_to_id RecordOverflow = 22
alert_description_to_id HandshakeFailure = 40
alert_description_to_id BadCertificate = 42
alert_description_to_id UnsupportedCertificate = 43
alert_description_to_id CertificateRevoked = 44
alert_description_to_id CertificateExpired = 45
alert_description_to_id CertificateUnknown = 46
alert_description_to_id IllegalParameter = 47
alert_description_to_id UnknownCA = 48
alert_description_to_id AccessDenied = 49
alert_description_to_id DecodeError = 50
alert_description_to_id DecryptError = 51
alert_description_to_id ProtocolVersion = 70
alert_description_to_id InsufficientSecurity = 71
alert_description_to_id InternalError = 80
alert_description_to_id InappropriateFallback = 86
alert_description_to_id UserCanceled = 90
alert_description_to_id MissingExtension = 109
alert_description_to_id UnsupportedExtension = 110
alert_description_to_id UnrecognizedName = 112
alert_description_to_id BadCertificateStatusResponse = 113
alert_description_to_id UnknownPskIdentity = 115
alert_description_to_id CertificateRequired = 116
alert_description_to_id NoApplicationProtocol = 120

public export
id_to_alert_description : Bits8 -> Maybe AlertDescription
id_to_alert_description 0 = Just CloseNotify
id_to_alert_description 10 = Just UnexpectedMessage
id_to_alert_description 20 = Just BadRecordMac
id_to_alert_description 22 = Just RecordOverflow
id_to_alert_description 40 = Just HandshakeFailure
id_to_alert_description 42 = Just BadCertificate
id_to_alert_description 43 = Just UnsupportedCertificate
id_to_alert_description 44 = Just CertificateRevoked
id_to_alert_description 45 = Just CertificateExpired
id_to_alert_description 46 = Just CertificateUnknown
id_to_alert_description 47 = Just IllegalParameter
id_to_alert_description 48 = Just UnknownCA
id_to_alert_description 49 = Just AccessDenied
id_to_alert_description 50 = Just DecodeError
id_to_alert_description 51 = Just DecryptError
id_to_alert_description 70 = Just ProtocolVersion
id_to_alert_description 71 = Just InsufficientSecurity
id_to_alert_description 80 = Just InternalError
id_to_alert_description 86 = Just InappropriateFallback
id_to_alert_description 90 = Just UserCanceled
id_to_alert_description 109 = Just MissingExtension
id_to_alert_description 110 = Just UnsupportedExtension
id_to_alert_description 112 = Just UnrecognizedName
id_to_alert_description 113 = Just BadCertificateStatusResponse
id_to_alert_description 115 = Just UnknownPskIdentity
id_to_alert_description 116 = Just CertificateRequired
id_to_alert_description 120 = Just NoApplicationProtocol
id_to_alert_description _ = Nothing

public export
data SupportedGroup : Type where
  X25519 : SupportedGroup
  X448 : SupportedGroup
  SECP256r1 : SupportedGroup
  SECP384r1 : SupportedGroup
  SECP521r1 : SupportedGroup

public export
Eq SupportedGroup where
  X25519    == X25519    = True
  X448      == X448      = True
  SECP256r1 == SECP256r1 = True
  SECP384r1 == SECP384r1 = True
  SECP521r1 == SECP521r1 = True
  _ == _ = False

public export
Show SupportedGroup where
  show X25519    = "X25519"
  show X448      = "X448"
  show SECP256r1 = "SECP256r1"
  show SECP384r1 = "SECP384r1"
  show SECP521r1 = "SECP521r1"

public export
supported_group_to_id : SupportedGroup -> (Bits8, Bits8)
supported_group_to_id X25519 = (0x00, 0x1d)
supported_group_to_id X448 = (0x00, 0x1e)
supported_group_to_id SECP256r1 = (0x00, 0x17)
supported_group_to_id SECP384r1 = (0x00, 0x18)
supported_group_to_id SECP521r1 = (0x00, 0x19)

public export
id_to_supported_group : (Bits8, Bits8) -> Maybe SupportedGroup
id_to_supported_group (0x00, 0x1d) = Just X25519
id_to_supported_group (0x00, 0x1e) = Just X448
id_to_supported_group (0x00, 0x17) = Just SECP256r1
id_to_supported_group (0x00, 0x18) = Just SECP384r1
id_to_supported_group (0x00, 0x19) = Just SECP521r1
id_to_supported_group _ = Nothing

public export
curve_group_to_type : SupportedGroup -> (DPair Type ECDHCyclicGroup)
curve_group_to_type X25519 = MkDPair X25519_DH %search
curve_group_to_type X448 = MkDPair X448_DH %search
curve_group_to_type SECP256r1 = MkDPair P256 %search
curve_group_to_type SECP384r1 = MkDPair P384 %search
curve_group_to_type SECP521r1 = MkDPair P521 %search

public export
curve_group_to_scalar_type : SupportedGroup -> Type
curve_group_to_scalar_type group = Scalar @{snd $ curve_group_to_type group}

public export
curve_group_to_element_type : SupportedGroup -> Type
curve_group_to_element_type group = Element @{snd $ curve_group_to_type group}

public export
data SignatureAlgorithm : Type where
  ECDSA_SECP256r1_SHA256 : SignatureAlgorithm
  RSA_PSS_RSAE_SHA256    : SignatureAlgorithm
  RSA_PKCS1_SHA256       : SignatureAlgorithm

public export
Show SignatureAlgorithm where
  show ECDSA_SECP256r1_SHA256 = "ECDSA_SECP256r1_SHA256"
  show RSA_PSS_RSAE_SHA256 = "RSA_PSS_RSAE_SHA256"
  show RSA_PKCS1_SHA256 = "RSA_PKCS1_SHA256"

public export
signature_algorithm_to_id : SignatureAlgorithm -> (Bits8, Bits8)
signature_algorithm_to_id ECDSA_SECP256r1_SHA256 = (0x04, 0x03)
signature_algorithm_to_id RSA_PSS_RSAE_SHA256 = (0x08, 0x04)
signature_algorithm_to_id RSA_PKCS1_SHA256 = (0x04, 0x01)

public export
id_to_signature_algorithm : (Bits8, Bits8) -> Maybe SignatureAlgorithm
id_to_signature_algorithm (0x04, 0x03) = Just ECDSA_SECP256r1_SHA256
id_to_signature_algorithm (0x08, 0x04) = Just RSA_PSS_RSAE_SHA256
id_to_signature_algorithm (0x04, 0x01) = Just RSA_PKCS1_SHA256
id_to_signature_algorithm _ = Nothing

public export
data CompressionLevel : Type where
  Null : CompressionLevel

public export
Show CompressionLevel where
  show Null = "Null"

public export
compression_level_to_id : CompressionLevel -> Bits8
compression_level_to_id Null = 0x00

public export
id_to_compression_level : Bits8 -> Maybe CompressionLevel
id_to_compression_level 0x00 = Just Null
id_to_compression_level _ = Nothing

public export
data CipherSuite : Type where
  ||| TLS 1.3 Cipher Suites
  TLS_AES_128_GCM_SHA256 : CipherSuite
  TLS_AES_256_GCM_SHA384 : CipherSuite
  -- TLS_CHACHA20_POLY1305_SHA256 : CipherSuite
  ||| TLS 1.2 Cipher Suites
  TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 : CipherSuite
  TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 : CipherSuite
  TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 : CipherSuite
  TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 : CipherSuite

public export
Show CipherSuite where
  show TLS_AES_128_GCM_SHA256 = "TLS_AES_128_GCM_SHA256"
  show TLS_AES_256_GCM_SHA384 = "TLS_AES_256_GCM_SHA384"
  -- show TLS_CHACHA20_POLY1305_SHA256 = "TLS_CHACHA20_POLY1305_SHA256"
  show TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 = "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256"
  show TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 = "TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384"
  show TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 = "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256"
  show TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = "TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384"

public export
cipher_suite_to_id : CipherSuite -> (Bits8, Bits8)
cipher_suite_to_id TLS_AES_128_GCM_SHA256 = (0x13, 0x01)
cipher_suite_to_id TLS_AES_256_GCM_SHA384 = (0x13, 0x02)
-- cipher_suite_to_id TLS_CHACHA20_POLY1305_SHA256 = (0x13, 0x03)
cipher_suite_to_id TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 = (0xc0, 0x2f)
cipher_suite_to_id TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 = (0xc0, 0x30)
cipher_suite_to_id TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 = (0xc0, 0x2b)
cipher_suite_to_id TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = (0xc0, 0x2c)

public export
id_to_cipher_suite : (Bits8, Bits8) -> Maybe CipherSuite
id_to_cipher_suite (0x13, 0x01) = Just TLS_AES_128_GCM_SHA256
id_to_cipher_suite (0x13, 0x02) = Just TLS_AES_256_GCM_SHA384
-- id_to_cipher_suite (0x13, 0x03) = Just TLS_CHACHA20_POLY1305_SHA256
id_to_cipher_suite (0xc0, 0x2f) = Just TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
id_to_cipher_suite (0xc0, 0x30) = Just TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
id_to_cipher_suite (0xc0, 0x2b) = Just TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
id_to_cipher_suite (0xc0, 0x2c) = Just TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
id_to_cipher_suite _ = Nothing

public export
ciphersuite_to_hash_type : CipherSuite -> (DPair Type Hash)
ciphersuite_to_hash_type TLS_AES_128_GCM_SHA256 = MkDPair Sha256 %search
ciphersuite_to_hash_type TLS_AES_256_GCM_SHA384 = MkDPair Sha384 %search
-- ciphersuite_to_hash_type TLS_CHACHA20_POLY1305_SHA256 = MkDPair Sha256 %search
ciphersuite_to_hash_type TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 = MkDPair Sha256 %search
ciphersuite_to_hash_type TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 = MkDPair Sha384 %search
ciphersuite_to_hash_type TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 = MkDPair Sha256 %search
ciphersuite_to_hash_type TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = MkDPair Sha384 %search

public export
ciphersuite_to_prf_type : CipherSuite -> (DPair Type Hash)
ciphersuite_to_prf_type TLS_AES_256_GCM_SHA384 = MkDPair Sha384 %search
ciphersuite_to_prf_type TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 = MkDPair Sha384 %search
ciphersuite_to_prf_type TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = MkDPair Sha384 %search
ciphersuite_to_prf_type _ = MkDPair Sha256 %search

public export
ciphersuite_to_mac_key_len : CipherSuite -> Nat
ciphersuite_to_mac_key_len _ = 0

public export
ciphersuite_to_iv_len : CipherSuite -> Nat
ciphersuite_to_iv_len _ = 4

public export
ciphersuite_to_verify_data_len : CipherSuite -> Nat
ciphersuite_to_verify_data_len _ = 12

public export
ciphersuite_to_aead_type : CipherSuite -> (DPair Type AEAD)
ciphersuite_to_aead_type TLS_AES_128_GCM_SHA256 = MkDPair TLS13_AES_128_GCM %search
ciphersuite_to_aead_type TLS_AES_256_GCM_SHA384 = MkDPair TLS13_AES_256_GCM %search
-- ciphersuite_to_aead_type TLS_CHACHA20_POLY1305_SHA256 = MkDPair ChaCha20_Poly1305 %search

ciphersuite_to_aead_type TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 = MkDPair TLS12_AES_128_GCM %search
ciphersuite_to_aead_type TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 = MkDPair TLS12_AES_256_GCM %search
ciphersuite_to_aead_type TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 = MkDPair TLS12_AES_128_GCM %search
ciphersuite_to_aead_type TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = MkDPair TLS12_AES_256_GCM %search

public export
data TLSVersion : Type where
  TLS10 : TLSVersion
  TLS11 : TLSVersion
  TLS12 : TLSVersion
  TLS13 : TLSVersion

public export
Eq TLSVersion where
  TLS10 == TLS10 = True
  TLS11 == TLS11 = True
  TLS12 == TLS12 = True
  TLS13 == TLS13 = True
  _ == _ = False

public export
Show TLSVersion where
  show TLS10 = "TLS10"
  show TLS11 = "TLS11"
  show TLS12 = "TLS12"
  show TLS13 = "TLS13"

public export
tls_version_to_id : TLSVersion -> (Bits8, Bits8)
tls_version_to_id TLS10 = (0x03, 0x01)
tls_version_to_id TLS11 = (0x03, 0x02)
tls_version_to_id TLS12 = (0x03, 0x03)
tls_version_to_id TLS13 = (0x03, 0x04)

public export
id_to_tls_version : (Bits8, Bits8) -> Maybe TLSVersion
id_to_tls_version (0x03, 0x01) = Just TLS10
id_to_tls_version (0x03, 0x02) = Just TLS11
id_to_tls_version (0x03, 0x03) = Just TLS12
id_to_tls_version (0x03, 0x04) = Just TLS13
id_to_tls_version _ = Nothing

public export
Ord TLSVersion where
  compare a b =
    let (_, av) = tls_version_to_id a
        (_, bv) = tls_version_to_id b
    in compare av bv

public export
data ExtensionType : Type where
  ServerName : ExtensionType
  SupportedGroups : ExtensionType
  SupportedVersions : ExtensionType
  SignatureAlgorithms : ExtensionType
  KeyShare : ExtensionType
  Unknown : (Bits8, Bits8) -> ExtensionType

public export
Show ExtensionType where
  show ServerName          = "ServerName"
  show SupportedGroups     = "SupportedGroups"
  show SupportedVersions   = "SupportedVersions"
  show SignatureAlgorithms = "SignatureAlgorithms"
  show KeyShare            = "KeyShare"
  show (Unknown (a, b))    = "Unknown " <+> show_hex a <+> " " <+> show_hex b

public export
extension_type_to_id : ExtensionType -> (Bits8, Bits8)
extension_type_to_id ServerName          = (0x00, 0x00)
extension_type_to_id SupportedGroups     = (0x00, 0x0a)
extension_type_to_id SignatureAlgorithms = (0x00, 0x0d)
extension_type_to_id SupportedVersions   = (0x00, 0x2b)
extension_type_to_id KeyShare            = (0x00, 0x33)
extension_type_to_id (Unknown x)         = x

public export
id_to_extension_type : (Bits8, Bits8) -> ExtensionType
id_to_extension_type (0x00, 0x00) = ServerName
id_to_extension_type (0x00, 0x0a) = SupportedGroups
id_to_extension_type (0x00, 0x0d) = SignatureAlgorithms
id_to_extension_type (0x00, 0x2b) = SupportedVersions
id_to_extension_type (0x00, 0x33) = KeyShare
id_to_extension_type x = Unknown x

public export
data HandshakeType : Type where
  ClientHello : HandshakeType
  ServerHello : HandshakeType
  NewSessionTicket : HandshakeType
  EncryptedExtensions : HandshakeType
  Certificate : HandshakeType
  CertificateVerify : HandshakeType
  Finished : HandshakeType
  ServerKeyExchange : HandshakeType
  ServerHelloDone : HandshakeType
  ClientKeyExchange : HandshakeType

public export
Show HandshakeType where
  show ClientHello = "ClientHello"
  show ServerHello = "ServerHello"
  show NewSessionTicket = "NewSessionTicket"
  show EncryptedExtensions = "EncryptedExtensions"
  show Certificate = "Certificate"
  show CertificateVerify = "CertificateVerify"
  show Finished = "Finished"
  show ServerKeyExchange = "ServerKeyExchange"
  show ServerHelloDone = "ServerHelloDone"
  show ClientKeyExchange = "ClientKeyExchange"

public export
handshake_type_to_id : HandshakeType -> Bits8
handshake_type_to_id ClientHello = 0x01
handshake_type_to_id ServerHello = 0x02
handshake_type_to_id NewSessionTicket = 0x04
handshake_type_to_id EncryptedExtensions = 0x08
handshake_type_to_id Certificate = 0x0b
handshake_type_to_id CertificateVerify = 0x0f
handshake_type_to_id Finished = 0x14
handshake_type_to_id ServerKeyExchange = 0x0c
handshake_type_to_id ServerHelloDone = 0x0e
handshake_type_to_id ClientKeyExchange = 0x10

public export
id_to_handshake_type : Bits8 -> Maybe HandshakeType
id_to_handshake_type 0x01 = Just ClientHello
id_to_handshake_type 0x02 = Just ServerHello
id_to_handshake_type 0x04 = Just NewSessionTicket
id_to_handshake_type 0x08 = Just EncryptedExtensions
id_to_handshake_type 0x0b = Just Certificate
id_to_handshake_type 0x0f = Just CertificateVerify
id_to_handshake_type 0x14 = Just Finished
id_to_handshake_type 0x0c = Just ServerKeyExchange
id_to_handshake_type 0x0e = Just ServerHelloDone
id_to_handshake_type 0x10 = Just ClientKeyExchange
id_to_handshake_type _ = Nothing

public export
data RecordType : Type where
  ChangeCipherSpec : RecordType
  Handshake : RecordType
  ApplicationData : RecordType
  Alert : RecordType

public export
Eq RecordType where
  ChangeCipherSpec == ChangeCipherSpec = True
  Handshake == Handshake = True
  ApplicationData == ApplicationData = True
  Alert == Alert = True
  _ == _ = False

public export
Show RecordType where
  show ChangeCipherSpec = "ChangeCipherSpec"
  show Handshake = "Handshake"
  show ApplicationData = "ApplicationData"
  show Alert = "Alert"

public export
record_type_to_id : RecordType -> Bits8
record_type_to_id ChangeCipherSpec = 0x14
record_type_to_id Handshake = 0x16
record_type_to_id ApplicationData = 0x17
record_type_to_id Alert = 0x15

public export
id_to_record_type : Bits8 -> Maybe RecordType
id_to_record_type 0x14 = Just ChangeCipherSpec
id_to_record_type 0x15 = Just Alert
id_to_record_type 0x16 = Just Handshake
id_to_record_type 0x17 = Just ApplicationData
id_to_record_type _ = Nothing

namespace Parsing
  ||| creates a parserializer given an isomorphism from a type to a constant
  export
  magic : (Cons (Posed Bits8) i, Monoid i) => {k : Nat} -> (a -> Vect (S k) Bits8) -> (Vect (S k) Bits8 -> Maybe a) -> Parserializer Bits8 i (SimpleError String) a
  magic encode decode = MkParserializer (toList . encode) $ do
    bs <- count (S k) token
    let bytes = map get bs
    let Just phi = decode bytes
    | Nothing =>
      let
        (begin, end) = mapHom pos (head bs, last bs)
      in
        fail $ msg $ "at position " <+> show begin <+> "-" <+> show end <+> ", unknown id: " <+> xxd (toList bytes)
    pure phi

  export
  alert_level : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) AlertLevel
  alert_level = under "alert level" $ magic (to_vect . alert_level_to_id) (id_to_alert_level . from_vect)

  export
  alert_description : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) AlertDescription
  alert_description = magic (to_vect . alert_description_to_id) (id_to_alert_description . from_vect)

  export
  tls_version : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) TLSVersion
  tls_version = under "tls version" $ magic (pair_to_vect . tls_version_to_id) (id_to_tls_version . vect_to_pair)

  export
  cipher_suite : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) CipherSuite
  cipher_suite = under "cipher suite" $ magic (pair_to_vect . cipher_suite_to_id) (id_to_cipher_suite . vect_to_pair)

  export
  supported_group : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) SupportedGroup
  supported_group = under "supported group" $ magic (pair_to_vect . supported_group_to_id) (id_to_supported_group . vect_to_pair)

  export
  signature_algorithm : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) SignatureAlgorithm
  signature_algorithm = under "signature algorithm" $ magic (pair_to_vect . signature_algorithm_to_id) (id_to_signature_algorithm . vect_to_pair)

  export
  compression_level : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) CompressionLevel
  compression_level = under "compression level" $ magic (to_vect . compression_level_to_id) (id_to_compression_level . from_vect)

  public export
  extension_type : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) ExtensionType
  extension_type = under "extension type" $ magic (pair_to_vect . extension_type_to_id) (Just . id_to_extension_type . vect_to_pair)

  public export
  handshake_type : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) HandshakeType
  handshake_type = under "handshake type" $ magic (to_vect . handshake_type_to_id) (id_to_handshake_type . from_vect)

  export
  record_type : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) RecordType
  record_type = under "record type" $ magic (to_vect . record_type_to_id) (id_to_record_type . from_vect)
