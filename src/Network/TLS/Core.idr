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
import Data.DPair
import Network.Socket
import Network.TLS.Record
import Utils.Bytes
import Utils.Misc
import Utils.Network
import Utils.Parser
import Decidable.Equality

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
ciphersuite_to_hash_type : CipherSuite -> (DPair Type Hash)
ciphersuite_to_hash_type TLS_AES_128_GCM_SHA256 = MkDPair Sha256 %search
ciphersuite_to_hash_type TLS_AES_256_GCM_SHA384 = MkDPair Sha384 %search
ciphersuite_to_hash_type TLS_CHACHA20_POLY1305_SHA256 = MkDPair Sha256 %search
ciphersuite_to_hash_type TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 = MkDPair Sha256 %search
ciphersuite_to_hash_type TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 = MkDPair Sha384 %search
ciphersuite_to_hash_type TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 = MkDPair Sha256 %search
ciphersuite_to_hash_type TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = MkDPair Sha384 %search

public export
curve_group_to_type : SupportedGroup -> (DPair Type ECDHCyclicGroup)
curve_group_to_type X25519 = MkDPair X25519_DH %search
curve_group_to_type X448 = MkDPair X448_DH %search
curve_group_to_type SECP256r1 = MkDPair P256 %search
curve_group_to_type SECP384r1 = MkDPair P384 %search
curve_group_to_type SECP521r1 = MkDPair P521 %search

public export
curve_group_to_keypair_type : (g : SupportedGroup) -> Type
curve_group_to_keypair_type group =
  let (ecdh ** _) = curve_group_to_type group
  in (Scalar {a=ecdh}, Element {a=ecdh})

public export
curve_group_to_scalar_type : SupportedGroup -> Type
curve_group_to_scalar_type group = Scalar @{(snd $ curve_group_to_type group)}

public export
curve_group_to_element_type : SupportedGroup -> Type
curve_group_to_element_type group = Element @{(snd $ curve_group_to_type group)}

public export
deserialize_key : SupportedGroup -> List Bits8 -> 
                  DPair Type $ \a => DPair (ECDHCyclicGroup a) $ \wit => Maybe (Element @{wit})
deserialize_key group input =
  let
    (a ** dhc) = curve_group_to_type group
  in
    (a ** dhc ** deserialize_pk @{dhc} input)

public export
record TLSInitalState where
  constructor MkTLSInitalState
  server_hostname : String
  client_random : Vect 32 Bits8
  session_id : List Bits8
  cipher_suites : List1 CipherSuite
  signature_algos : List1 SignatureAlgorithm
  dh_keys : List1 (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))

public export
record TLSClientHelloState where
  constructor MkTLSClientHelloState
  b_client_hello : List Bits8
  client_random : Vect 32 Bits8
  dh_keys : List1 (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))

public export
record TLS3ServerHelloState where
  constructor MkTLS3ServerHelloState
  digest_state : Hash a => a
  shared_secret : List Bits8
  cipher_suite : CipherSuite

-- TODO: TLS2 Support
public export
record TLS2ServerHelloState where
  constructor MkTLS2ServerHelloState
  client_random : Vect 32 Bits8
  server_random : Vect 32 Bits8
  cipher_suite  : CipherSuite

public export
data TLSStep : Type where
  Init : TLSStep
  ClientHello : TLSStep
  ServerHello2 : TLSStep
  ServerHello3 : TLSStep

public export
data TLSState : TLSStep -> Type where
  TLS_Init : TLSInitalState -> TLSState Init
  TLS_ClientHello : TLSClientHelloState -> TLSState ClientHello
  TLS3_ServerHello : TLS3ServerHelloState -> TLSState ServerHello3
  TLS2_ServerHello : TLS2ServerHelloState -> TLSState ServerHello2

encode_public_keys : (g : SupportedGroup) -> Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g) -> 
                     (SupportedGroup, List Bits8)
encode_public_keys group (sk, pk) = (group, serialize_pk @{(snd $ curve_group_to_type group)} pk)

key_exchange : (group : SupportedGroup) -> 
               List Bits8 ->
               List (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g))) ->
               Maybe (List Bits8)
key_exchange group pk [] = Nothing
key_exchange group pk ((group' ** (sk, _)) :: xs) =
  case decEq @{FromEq} group group' of
    Yes _ => deserialize_then_dh @{(snd $ curve_group_to_type group')} sk pk
    No _ => key_exchange group pk xs

public export
tls_init_to_clienthello : TLSState Init -> (Message.ClientHello, TLSState ClientHello)
tls_init_to_clienthello (TLS_Init state) = 
  let client_hello_object = MkClientHello
        TLS12
        state.client_random
        state.session_id
        state.cipher_suites
        (singleton Null)
        [ (_ ** ServerName $ DNS state.server_hostname ::: [])
        , (_ ** SupportedGroups $ map fst state.dh_keys)
        , (_ ** SignatureAlgorithms state.signature_algos)
        , (_ ** KeyShare $ map (uncurry encode_public_keys) state.dh_keys)
        , (_ ** SupportedVersions $ TLS13 ::: [])
        ]
      b_client_hello = 
        (arecord {i = List (Posed Bits8)}).encode (TLS12, (_ ** Handshake [(_ ** ClientHello client_hello_object)]))
  in (client_hello_object, TLS_ClientHello $ MkTLSClientHelloState (drop 5 b_client_hello) state.client_random state.dh_keys)

public export
tls_clienthello_to_serverhello : TLSState ClientHello -> ServerHello -> List Bits8 ->
                                 Either String (Either (TLSState ServerHello2) (TLSState ServerHello3))
tls_clienthello_to_serverhello (TLS_ClientHello state) server_hello b_server_hello =
  case get_server_version server_hello of
    TLS13 => do
      let (hash_algo ** _) = ciphersuite_to_hash_type server_hello.cipher_suite
      let digest_state = update b_server_hello $ update state.b_client_hello $ init hash_algo
      (group, pk) <- get_server_handshake_key server_hello
      shared_secret <- maybe_to_either (key_exchange group pk $ toList state.dh_keys) "server sent invalid key"
      Right $ Right $ TLS3_ServerHello $ MkTLS3ServerHelloState digest_state shared_secret server_hello.cipher_suite
    TLS12 =>
      Right
      $ Left
      $ TLS2_ServerHello
      $ MkTLS2ServerHelloState state.client_random server_hello.random server_hello.cipher_suite
    tlsvr => Left $ "unsupported version: " <+> show tlsvr
