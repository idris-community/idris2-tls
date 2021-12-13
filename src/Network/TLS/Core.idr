module Network.TLS.Core

import Crypto.AEAD
import Crypto.AES
import Crypto.Curve
import Crypto.Curve.Weierstrass
import Crypto.Curve.XCurves
import Crypto.ECDH
import Crypto.HKDF
import Crypto.Hash
import Crypto.Random
import Data.Bits
import Data.List
import Data.List1
import Data.Vect
import Network.Socket
import Network.TLS.Record
import Utils.Bytes
import Utils.Misc
import Utils.Network
import Utils.Parser

public export
tls13_supported_cipher_suites : List1 CipherSuite
tls13_supported_cipher_suites =
  TLS_AES_128_GCM_SHA256 ::: [TLS_AES_256_GCM_SHA384, TLS_CHACHA20_POLY1305_SHA256]

public export
tls12_supported_cipher_suites : List1 CipherSuite
tls12_supported_cipher_suites =
  TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 :::
  [ TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
  , TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
  , TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ]

public export
supported_groups : List1 SupportedGroup
supported_groups = X25519 ::: [SECP256r1, X448, SECP384r1, SECP521r1]

public export
supported_signature_algorithms : List1 SignatureAlgorithm
supported_signature_algorithms = ECDSA_SECP256r1_SHA256 ::: [RSA_PSS_RSAE_SHA256, RSA_PKCS1_SHA256]

public export
get_server_version : ServerHello -> TLSVersion
get_server_version hello = go hello.extensions
  where
  go : List (DPair _ ServerExtension) -> TLSVersion
  go [] = hello.version
  go ((SupportedVersions ** (SupportedVersions version)) :: xs) = version
  go (x :: xs) = go xs

public export
get_server_handshake_key : ServerHello -> Either String (SupportedGroup, List Bits8)
get_server_handshake_key hello = go hello.extensions
  where
  go : List (DPair _ ServerExtension) -> Either String (SupportedGroup, List Bits8)
  go [] = Left "Server did not return any handshake keys"
  go ((KeyShare ** (KeyShare x)) :: xs) = Right x
  go (x :: xs) = go xs

public export
curve_group_to_type : SupportedGroup -> (DPair Type ECDHCyclicGroup)
curve_group_to_type X25519 = MkDPair X25519_DH %search
curve_group_to_type X448 = MkDPair X448_DH %search
curve_group_to_type SECP256r1 = MkDPair P256 %search
curve_group_to_type SECP384r1 = MkDPair P384 %search
curve_group_to_type SECP521r1 = MkDPair P521 %search

public export
curve_group_to_keypair_type : (g : SupportedGroup) -> Type
curve_group_to_keypair_type X25519 = (Scalar {a=X25519_DH}, Element {a=X25519_DH})
curve_group_to_keypair_type X448   = (Scalar {a=X448_DH}, Element {a=X448_DH})
curve_group_to_keypair_type SECP256r1 = (Scalar {a=P256}, Element {a=P256})
curve_group_to_keypair_type SECP384r1 = (Scalar {a=P384}, Element {a=P384})
curve_group_to_keypair_type SECP521r1 = (Scalar {a=P521}, Element {a=P521})

public export
deserialize_key : SupportedGroup -> List Bits8 -> 
                  DPair Type $ \a => DPair (ECDHCyclicGroup a) $ \wit => Maybe (Element @{wit})
deserialize_key group input =
  let
    (a ** dhc) = curve_group_to_type group
  in
    (a ** dhc ** deserialize_pk @{dhc} input)

-- public export
-- record TLSInitalState where
--   constructor MkTLSInitalState
--   random : Vect 32 Bits8
--   session_id : List Bits8
--   cipher_suites : List1 CipherSuite
--   dh_keys : List1 (DPair SupportedGroup curve_group_to_keypair_type)
-- 
-- public export
-- data TLSStep : Type where
--   Init : TLSStep
-- 
-- public export
-- data TLSState : TLSStep -> Type where
--   TLS_Init : TLSInitalState -> TLSState Init
-- 
-- public export
-- tls_init_hello : MonadRandom m => String -> TLSState Init -> m (Handshake ClientHello)
-- tls_init_hello hostname (TLS_Init state) = do
--   random <- random_bytes _
--   session_id <- random_bytes 0x20 -- randomly generated for now until we implement PSK
--   pure $ ClientHello $ MkClientHello
--     TLS12 -- Always set to 1.2 as per the 1.3 spec
--     random
--     (toList session_id)
--     ( TLS_AES_128_GCM_SHA256 ::: [ TLS_AES_256_GCM_SHA384, TLS_CHACHA20_POLY1305_SHA256 ])
--     (singleton Null) -- We have zero intention of implementing compression
--     [ ServerName $ MkServerName $ DNS hostname ::: []
--     , SupportedGroups $ MkServerName supported_groups
--     , SignatureAlgorithms $ MkServerName $ RSA_PKCS1_SHA256 ::: [RSA_PSS_RSAE_SHA256]
--     , KeyShare $ Mk $ map ?tls_init_hello_hole $ dh_keys state
--     , SupportedVersions $ Mk $ TLS13 ::: []
--     ]
