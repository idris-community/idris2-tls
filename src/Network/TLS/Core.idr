module Network.TLS.Core

import Crypto.AEAD
import Crypto.AES
import Crypto.Curve
import Crypto.Curve.Weierstrass
import Crypto.Curve.XCurves
import Crypto.ECDH
import Network.TLS.HKDF
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
import Utils.Parser
import Control.Monad.Error.Either

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
record TLSInitialState where
  constructor MkTLSInitialState
  server_hostname : String
  client_random : Vect 32 Bits8
  session_id : List Bits8
  cipher_suites : List1 CipherSuite
  signature_algos : List1 SignatureAlgorithm
  dh_keys : List1 (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))

export
record TLSClientHelloState where
  constructor MkTLSClientHelloState
  b_client_hello : List Bits8
  client_random : Vect 32 Bits8
  dh_keys : List1 (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))

export
data TLS3ServerHelloState : (aead : Type) -> AEAD aead -> (algo : Type) -> Hash algo -> Type where
  MkTLS3ServerHelloState : (a' : AEAD a) -> (h' : Hash h) -> h ->
                           HandshakeKeys (iv_bytes {a=a}) (key_bytes {a=a}) -> Nat -> TLS3ServerHelloState a a' h h'

export
data TLS3ApplicationState : (aead : Type) -> AEAD aead -> Type where
  MkTLS3ApplicationState : (a' : AEAD a) -> ApplicationKeys (iv_bytes {a=a}) (key_bytes {a=a}) -> Nat -> Nat -> TLS3ApplicationState a a'

export
record TLS2ServerHelloState algo where
  constructor MkTLS2ServerHelloState
  client_random : Vect 32 Bits8
  server_random : Vect 32 Bits8
  cipher_suite  : CipherSuite
  dh_keys : List1 (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))
  digest_wit : Hash algo
  digest_state : algo

export
record TLS2ServerCertificateState algo where
  constructor MkTLS2ServerCertificateState
  server_hello : TLS2ServerHelloState algo
  certificate : Certificate
  cipher_suite : CipherSuite
  dh_keys : List1 (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))
  digest_wit : Hash algo
  digest_state : algo

export
data TLS2ServerKEXState : (mac_key_len : Nat) -> (aead : Type) -> AEAD aead -> (algo : Type) -> Hash algo -> Type where
  MkTLS2ServerKEXState : (a' : AEAD a) -> (h' : Hash h) -> h -> Nat -> List Bits8 ->
                         (Application2Keys (iv_bytes @{a'}) (key_bytes @{a'}) mac_key_len) ->
                         TLS2ServerKEXState mac_key_len a a' h h'

public export
data TLSStep : Type where
  Init : TLSStep
  ClientHello : TLSStep
  ServerHello2 : TLSStep
  ServerHello3 : TLSStep
  Application3 : TLSStep
  ServerCert2 : TLSStep
  ServerKEX2 : TLSStep

public export
data TLSState : TLSStep -> Type where
  TLS_Init : TLSInitialState -> TLSState Init
  TLS_ClientHello : TLSClientHelloState -> TLSState ClientHello
  TLS3_ServerHello : TLS3ServerHelloState a b algo d -> TLSState ServerHello3
  TLS3_Application : TLS3ApplicationState a b -> TLSState Application3
  TLS2_ServerHello : TLS2ServerHelloState algo -> TLSState ServerHello2
  TLS2_ServerCertificate : TLS2ServerCertificateState algo -> TLSState ServerCert2
  TLS2_ServerKEX : TLS2ServerKEXState mac a b algo d -> TLSState ServerKEX2

encode_public_keys : (g : SupportedGroup) -> Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g) ->
                     (SupportedGroup, List Bits8)
encode_public_keys group (sk, pk) = (group, serialize_pk @{snd $ curve_group_to_type group} pk)

key_exchange : (group : SupportedGroup) ->
               List Bits8 ->
               List (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g))) ->
               Maybe (List Bits8)
key_exchange group pk [] = Nothing
key_exchange group pk ((group' ** (sk, _)) :: xs) =
  if group == group'
    then deserialize_then_dh @{snd $ curve_group_to_type group'} sk pk
    else key_exchange group pk xs

parse_record : List Bits8 ->
               (Parserializer Bits8 (List (Posed Bits8)) (SimpleError String) (Either (AlertLevel, AlertDescription) (TLSVersion, DPair _ Record))) ->
               Either String (DPair _ Record)
parse_record b_input parser = do
  let (Pure [] $ Right (TLS12, record')) = feed (map (uncurry MkPosed) $ enumerate Z b_input) parser.decode
  | (Pure [] $ Right (tlsver, _)) => Left $ "Unsupported TLS version: " <+> show tlsver
  | (Pure [] $ Left (_, alert)) => Left $ "TLS alert: " <+> show alert
  | (Pure leftover _) => Left $ "Parsing error: overfed, leftover: " <+> xxd (map get leftover)
  | (Fail err) => Left $ "Parsing error: " <+> show err
  | _ => Left "Parsing error: underfed"
  case record' of
    (_ ** Alert alert) => Left $ show alert
    ok => pure ok

public export
tls_init_to_clienthello : TLSState Init -> (List Bits8, TLSState ClientHello)
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
        , (_ ** SupportedVersions $ TLS13 ::: [ TLS12 ])
        ]
      b_client_hello =
        (arecord {i = List (Posed Bits8)}).encode (TLS12, (_ ** Handshake [(_ ** ClientHello client_hello_object)]))
  in (b_client_hello, TLS_ClientHello $ MkTLSClientHelloState (drop 5 b_client_hello) state.client_random state.dh_keys)

public export
tls_clienthello_to_serverhello : TLSState ClientHello -> List Bits8 ->
                                 Either String (Either (TLSState ServerHello2) (TLSState ServerHello3))
tls_clienthello_to_serverhello (TLS_ClientHello state) b_server_hello = do
  (MkDPair _ (Handshake [MkDPair _ (ServerHello server_hello)])) <- parse_record b_server_hello alert_or_arecord
  | _ => Left $ "Parsing error: record not server_hello"
  case get_server_version server_hello of
    TLS13 => do
      let (hash_algo ** hwit) = ciphersuite_to_hash_type server_hello.cipher_suite
      let digest_state = update (drop 5 b_server_hello) $ update state.b_client_hello $ init hash_algo
      (group, pk) <- get_server_handshake_key server_hello
      shared_secret <- maybe_to_either (key_exchange group pk $ toList state.dh_keys) "server sent invalid key"
      let (aead ** awit) = ciphersuite_to_aead_type server_hello.cipher_suite
      let hk = tls13_handshake_derive hash_algo (iv_bytes {a=aead}) (key_bytes {a=aead}) shared_secret $ toList $ finalize digest_state
      Right $ Right $ TLS3_ServerHello $ MkTLS3ServerHelloState awit hwit digest_state hk Z
    TLS12 =>
      let (hash_algo ** hwit) = ciphersuite_to_prf_type server_hello.cipher_suite
          digest_state = update (drop 5 b_server_hello) $ update state.b_client_hello $ init hash_algo
      in Right 
         $ Left 
         $ TLS2_ServerHello 
         $ MkTLS2ServerHelloState state.client_random server_hello.random server_hello.cipher_suite state.dh_keys hwit digest_state
    tlsvr => Left $ "unsupported version: " <+> show tlsvr

decrypt_hs_s_wrapper : TLS3ServerHelloState aead aead' algo algo' -> Wrapper (mac_bytes @{aead'}) -> List Bits8 ->
                       Maybe (TLS3ServerHelloState aead aead' algo algo', List Bits8)
decrypt_hs_s_wrapper (MkTLS3ServerHelloState a' h' digest_state hk counter) (MkWrapper ciphertext mac_tag) record_header =
  let s_hs_iv = zipWith xor hk.server_handshake_iv $ integer_to_be _ $ natToInteger counter
  in case decrypt @{a'} hk.server_handshake_key s_hs_iv ciphertext record_header $ toList mac_tag of
        (_, False) => Nothing
        (plaintext, True) => Just (MkTLS3ServerHelloState a' h' digest_state hk (S counter), plaintext)

list_minus : List a -> List b -> List a
list_minus a b = take (length a `minus` length b) a

tls3_serverhello_to_application_go : Monad m => TLSState ServerHello3 -> List Bits8 -> (Certificate -> m Bool) ->
                                              (EitherT String m (Either (TLSState ServerHello3) (List Bits8, TLSState Application3)))
tls3_serverhello_to_application_go og [] cert_ok = pure $ Left og
tls3_serverhello_to_application_go og@(TLS3_ServerHello {algo} server_hello@(MkTLS3ServerHelloState a' h' d' hk c')) plaintext cert_ok =
  case feed (map (uncurry MkPosed) $ enumerate Z plaintext) handshake.decode of
    Pure leftover (_ ** EncryptedExtensions x) =>
      let consumed = plaintext `list_minus` leftover
          new = TLS3_ServerHello $ MkTLS3ServerHelloState a' h' (update consumed d') hk c'
      in tls3_serverhello_to_application_go new (map get leftover) cert_ok
    Pure leftover (_ ** Certificate x) => do
      True <- MkEitherT $ map Right $ cert_ok x
      | False => throwE "cannot verify certificate"
      let consumed = plaintext `list_minus` leftover
      let new = TLS3_ServerHello $ MkTLS3ServerHelloState a' h' (update consumed d') hk c'
      tls3_serverhello_to_application_go new (map get leftover) cert_ok
    Pure leftover (_ ** CertificateVerify x) =>
      -- TODO: add code to check
      let consumed = plaintext `list_minus` leftover
          new = TLS3_ServerHello $ MkTLS3ServerHelloState a' h' (update consumed d') hk c'
      in tls3_serverhello_to_application_go new (map get leftover) cert_ok
    Pure [] (_ ** Finished x) =>
      if (tls13_verify_data algo hk.server_traffic_secret $ toList $ finalize d') == verify_data x
         then
           let digest = update plaintext d'
               client_verify_data = tls13_verify_data algo hk.client_traffic_secret $ toList $ finalize digest
               client_handshake_finished =
                 to_application_data
                 $ MkWrappedRecord Handshake ((with_id no_id_finished).encode {i = List (Posed Bits8)}
                 $ Finished
                 $ MkFinished client_verify_data)
               record_length = (length client_handshake_finished) + mac_bytes @{a'}
               b_record = record_type_with_version_with_length.encode {i = List (Posed Bits8)} (ApplicationData, TLS12, record_length)
               (chf_encrypted, chf_mac_tag) = encrypt @{a'} hk.client_handshake_key hk.client_handshake_iv client_handshake_finished b_record
               app_key = tls13_application_derive algo hk (toList $ finalize digest)
               verify_data_wrapped = MkWrapper chf_encrypted chf_mac_tag
               b_chf_wrapped =
                 (arecord {i = List (Posed Bits8)}).encode (TLS12, MkDPair _ (ApplicationData $ to_application_data $ MkWrapper chf_encrypted chf_mac_tag))
           in pure $ Right (b_chf_wrapped, TLS3_Application $ MkTLS3ApplicationState a' app_key Z Z)
         else
           throwE "verify data does not match"
    Fail err => throwE $ "body: " <+> xxd plaintext <+> "\nbody length: " <+> (show $ length plaintext) <+> "\nparsing error: " <+> show err
    _ => throwE "failed to parse plaintext"

public export
tls3_serverhello_to_application : Monad m => TLSState ServerHello3 -> List Bits8 -> (Certificate -> m Bool) ->
                                              m (Either String (Either (TLSState ServerHello3) (List Bits8, TLSState Application3)))
tls3_serverhello_to_application og@(TLS3_ServerHello server_hello@(MkTLS3ServerHelloState a' h' d' hk c')) b_wrapper cert_ok = runEitherT $ do
  let Right (MkDPair _ (ApplicationData application_data)) = parse_record b_wrapper alert_or_arecord
  | Right (MkDPair _ (ChangeCipherSpec _)) => pure $ Left og
  | Left err => throwE err
  | _ => throwE $ "Parsing error: record not application data"
  let Just wrapper = from_application_data {mac_size = (mac_bytes @{a'})} application_data
  | Nothing => throwE $ "malformed wrapper:" <+> xxd application_data
  let Just (server_hello, plaintext') = decrypt_hs_s_wrapper server_hello wrapper (take 5 b_wrapper)
  | Nothing => throwE "cannot decrypt wrapper"
  let Just (plaintext, 0x16) = uncons1 <$> toList1' plaintext'
  | Just ([_, alert], 0x15) => throwE $ "alert: " <+> (show $ id_to_alert_description alert)
  | Just (plaintext, i) => throwE $ "invalid record id: " <+> show i <+> " body: " <+> xxd plaintext
  | Nothing => throwE "plaintext is empty"
  tls3_serverhello_to_application_go (TLS3_ServerHello server_hello) plaintext cert_ok

decrypt_ap_s_wrapper : TLS3ApplicationState aead aead' -> Wrapper (mac_bytes @{aead'}) -> List Bits8 ->
                       Maybe (TLS3ApplicationState aead aead', List Bits8)
decrypt_ap_s_wrapper (MkTLS3ApplicationState a' ak c_counter s_counter) (MkWrapper ciphertext mac_tag) record_header =
  let s_ap_iv = zipWith xor ak.server_application_iv $ integer_to_be _ $ natToInteger s_counter
  in case decrypt @{a'} ak.server_application_key s_ap_iv ciphertext record_header $ toList mac_tag of
        (_, False) => Nothing
        (plaintext, True) => Just (MkTLS3ApplicationState a' ak c_counter (S s_counter), plaintext)

public export
decrypt_from_record : TLSState Application3 -> List Bits8 -> Either String (TLSState Application3, List Bits8)
decrypt_from_record og@(TLS3_Application app_state@(MkTLS3ApplicationState a' ak c_counter s_counter)) b_wrapper = do
  (MkDPair _ (ApplicationData application_data)) <- parse_record b_wrapper alert_or_arecord
  | _ => Left $ "Parsing error: record not application data"
  let Just wrapper = from_application_data {mac_size = (mac_bytes @{a'})} application_data
  | Nothing => Left $ "malformed wrapper:" <+> xxd application_data
  let Just (app_state, plaintext') = decrypt_ap_s_wrapper app_state wrapper (take 5 b_wrapper)
  | Nothing => Left "cannot decrypt wrapper"
  let Just (plaintext, 0x17) = uncons1 <$> toList1' plaintext'
  | Just (plaintext, 0x16) => Right (TLS3_Application app_state, []) -- implement session ticket in the future?
  | Just ([_, alert], 0x15) => Left $ "alert: " <+> (show $ id_to_alert_description alert)
  | Just (plaintext, i) => Left $ "invalid record id: " <+> show i <+> " body: " <+> xxd plaintext
  | Nothing => Left "plaintext is empty"
  Right (TLS3_Application app_state, plaintext)

public export
encrypt_to_record : TLSState Application3 -> List Bits8 -> (TLSState Application3, List Bits8)
encrypt_to_record (TLS3_Application $ MkTLS3ApplicationState a' ak c_counter s_counter) plaintext =
  let c_ap_iv = zipWith xor ak.client_application_iv $ integer_to_be _ $ natToInteger c_counter
      b_application_data = to_application_data $ MkWrappedRecord ApplicationData plaintext
      record_length = (length b_application_data) + mac_bytes @{a'}
      b_record_header = (record_type_with_version_with_length {i = List (Posed Bits8)}).encode (ApplicationData, TLS12, record_length)
      (app_encrypted, app_mac_tag) = encrypt @{a'} ak.client_application_key c_ap_iv b_application_data b_record_header
      b_app_wrapped = arecord.encode {i = List (Posed Bits8)} (TLS12, MkDPair _ (ApplicationData $ to_application_data $ MkWrapper app_encrypted app_mac_tag))
  in (TLS3_Application $ MkTLS3ApplicationState a' ak (S c_counter) s_counter, b_app_wrapped)

public export
serverhello2_to_servercert : TLSState ServerHello2 -> List Bits8 -> Either String (TLSState ServerCert2)
serverhello2_to_servercert (TLS2_ServerHello server_hello) b_cert = do
  (MkDPair _ (Handshake [MkDPair _ (Certificate server_cert)])) <- parse_record b_cert alert_or_arecord2
  | _ => Left $ "Parsing error: record not server_hello"
  Right $ TLS2_ServerCertificate 
        $ MkTLS2ServerCertificateState 
            server_hello 
            server_cert 
            server_hello.cipher_suite
            server_hello.dh_keys
            server_hello.digest_wit
            (update @{server_hello.digest_wit} (drop 5 b_cert) server_hello.digest_state)

public export
servercert_to_serverkex : TLSState ServerCert2 -> List Bits8 -> Either String (TLSState ServerKEX2)
servercert_to_serverkex (TLS2_ServerCertificate server_cert) b_kex = do
  (MkDPair _ (Handshake [MkDPair _ (ServerKeyExchange server_kex)])) <- parse_record b_kex alert_or_arecord2
  | _ => Left $ "Parsing error: record not server_hello"
  let Just shared_secret = key_exchange (server_kex.server_pk_group) (server_kex.server_pk_body) (toList server_cert.dh_keys)
  | Nothing => Left "cannot parse server public key"
  let (aead ** awit) = ciphersuite_to_aead_type server_cert.cipher_suite
  let app_key =
        tls12_application_derive server_cert.digest_wit
          (iv_bytes {a=aead})
          (key_bytes {a=aead})
          (ciphersuite_to_mac_key_len server_cert.cipher_suite)
          shared_secret
          (toList server_cert.server_hello.client_random)
          (toList server_cert.server_hello.server_random)
  let Just (_, chosen_pk) = find (\(g,_) => g == server_kex.server_pk_group) $ toList $ map (uncurry encode_public_keys) server_cert.dh_keys
  | Nothing => Left "cannot find public key that match the server's"
  -- TODO: check if key is signed by the certificate
  Right $ TLS2_ServerKEX 
        $ MkTLS2ServerKEXState 
            awit 
            server_cert.digest_wit 
            (update @{server_cert.digest_wit} (drop 5 b_kex) server_cert.digest_state)
            (ciphersuite_to_verify_data_len server_cert.cipher_suite)
            chosen_pk 
            app_key

encrypt_to_wrapper2 : AEAD a => Vect (key_bytes {a=a}) Bits8 -> Vect (iv_bytes {a=a}) Bits8 -> List Bits8 -> RecordType -> Nat -> List Bits8
encrypt_to_wrapper2 key iv plaintext record_id sequence =
  let aad = 
        (toList $ to_be {n=8} (cast {to=Bits64} sequence)) 
        <+> [record_type_to_id record_id, 0x03, 0x03] -- 0x03 0x03 is the byte representation of TLS 1.2
        <+> (toList $ to_be {n=2} (cast {to=Bits16} sequence))
      (ciphertext, mac) = encrypt key iv plaintext aad
      wrapper = MkWrapper2 iv ciphertext mac
  in (wrapper2 {i = List (Posed Bits8)}).encode (record_id, TLS12, wrapper)

public export
serverkex_process_serverhellodone : TLSState ServerKEX2 -> List Bits8 -> Either String (List Bits8, TLSState ServerKEX2)
serverkex_process_serverhellodone og@(TLS2_ServerKEX (MkTLS2ServerKEXState a' h' digest_state vdlen chosen_pk app_key)) b_hello_done = do
  (MkDPair _ (Handshake [MkDPair _ (ServerHelloDone _)])) <- parse_record b_hello_done alert_or_arecord2
  | _ => Left $ "Parsing error: record not server_hello"
  let b_client_kex =
        (arecord {i = List (Posed Bits8)}).encode (TLS12, (_ ** Handshake [(_ ** ClientKeyExchange $ MkClientKeyExchange chosen_pk)]))
  let b_client_change_cipher_spec =
        (arecord {i = List (Posed Bits8)}).encode (TLS12, (_ ** ChangeCipherSpec [0x01]))
  let digest_state =
        update (drop 5 b_client_kex) $ update (drop 5 b_hello_done) digest_state
  let client_verify_data = (with_id no_id_finished).encode {i = List (Posed Bits8)} 
        $ Finished 
        $ MkFinished 
        $ toList
        (tls12_verify_data h' vdlen (toList app_key.master_secret) (toList $ finalize digest_state))
  let b_client_verify_data =
        encrypt_to_wrapper2 app_key.client_application_key app_key.client_application_iv client_verify_data Handshake Z
  let digest_state =
        update (drop 5 b_client_verify_data) digest_state
  Right ( b_client_kex <+> b_client_change_cipher_spec <+> b_client_verify_data
        , TLS2_ServerKEX (MkTLS2ServerKEXState a' h' digest_state vdlen chosen_pk app_key))
