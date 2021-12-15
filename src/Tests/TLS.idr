module Tests.TLS

import Crypto.AEAD
import Crypto.Curve
import Crypto.Curve.Weierstrass
import Crypto.Curve.XCurves
import Crypto.ECDH
import Network.TLS.HKDF
import Crypto.Hash
import Crypto.Random
import Crypto.Random.C
import Data.Bits
import Data.List
import Data.List1
import Data.Nat.Factor
import Data.Vect
import Network.Socket
import Network.TLS
import Network.TLS.Record
import Utils.Bytes
import Utils.Misc
import Utils.Network
import Utils.Parser

-- TODO: FIX: takes about 1 second to compile for some reason
smart_read' : (Cons (Posed Bits8) i, Monoid i, HasIO m) => Socket -> Nat -> Parser i (SimpleError String) a -> m (List Bits8, (Either String a))
smart_read' sock pos (Pure leftover x) = do
  pure ([], Right x)
smart_read' sock pos (Fail err) = do
  pure ([], Left $ "parser stopped at position " <+> show pos <+> ": " <+> show err)
smart_read' sock pos parser = do
  Just bs <- recv_bytes sock 1
  | Nothing => pure ([], Left "recv_bytes failed")
  case bs of
    (b :: []) => map (mapFst (b ::)) $ smart_read' sock (S pos) (feed (singleton $ MkPosed pos b) parser)
    _ => pure $ (bs, Left $ "weird list returned from recv_byte: " <+> xxd bs)

-- inefficient but it is more pleasant to work with, can get stuck potentially
smart_read : (Cons (Posed Bits8) i, Monoid i, HasIO m) => Socket -> Parser i (SimpleError String) a -> m (List Bits8, Either String a)
smart_read sock parser = smart_read' sock 0 parser

test_http_body : String -> String
test_http_body hostname = "GET / HTTP/1.1\nHost: " <+> hostname <+> "\n\n"

example_hostname : String
example_hostname = "www.cloudflare.com"

-- TODO: FIX: takes about ~30 seconds to compile for some reason
partial
tls_test : HasIO m => (target_hostname : String) -> m ()
tls_test target_hostname = do
  Right sock <- socket AF_INET Stream 0
  | Left err => putStrLn $ "unable to create socket: " <+> show err

  putStrLn $ "generate key pair"
  -- (sk, pk) <- generate_key_pair {a=X25519_DH}
  let sk =
    [ 0xcc, 0x93, 0x5d, 0xb7, 0x60, 0x54, 0xe7, 0x2d, 0x3a, 0x29, 0xcb, 0x62, 0x5d, 0xc0, 0x10, 0xca, 0x6d
    , 0x46, 0x0e, 0xf6, 0x56, 0xf5, 0x06, 0xa5, 0xbb, 0x50, 0x4a, 0xb0, 0x68, 0x28, 0x34, 0x30]
  let pk =
    [ 0x38, 0xf3, 0xa1, 0xf3, 0xa8, 0x3b, 0x6c, 0x55, 0x88, 0x9a, 0x4b, 0x5d, 0x62, 0x81, 0x70, 0xf5, 0xe6
    , 0xca, 0x09, 0x60, 0xb9, 0x3b, 0x4a, 0xd8, 0x95, 0x59, 0x00, 0x2d, 0x72, 0x78, 0x9d, 0x24 ]

  putStrLn $ ("private key: " <+> (xxd $ toList sk))
  putStrLn $ ("public key: " <+> (xxd $ toList pk))

  putStrLn $ "connecting to " <+> target_hostname
  0 <- connect sock (Hostname target_hostname) 443
  | _ => putStrLn $ "unable to connect"
  putStrLn $ "connected"

  putStrLn $ "generating random"
  let random = map (cast . finToNat) range
  putStrLn $ "random: " <+> xxd (toList random)
  session <- random_bytes 0
  putStrLn $ "session: " <+> xxd (toList session)

  let
    client_hello_object =
      MkClientHello
        TLS12
        random
        (toList session)
        ( TLS_AES_128_GCM_SHA256 ::: [ TLS_AES_256_GCM_SHA384, TLS_CHACHA20_POLY1305_SHA256 ])
        (singleton Null)
        [ (_ ** ServerName $ DNS target_hostname ::: [])
        , (_ ** SupportedGroups $ X25519 ::: [SECP256r1])
        , (_ ** SignatureAlgorithms $ RSA_PKCS1_SHA256 ::: [RSA_PSS_RSAE_SHA256, ECDSA_SECP256r1_SHA256])
        , (_ ** KeyShare $ singleton (X25519, serialize_pk {a=X25519_DH} pk))
        , (_ ** SupportedVersions $ TLS13 ::: [])
        ]

  putStrLn $ "sending client hello"
  let b_client_hello = (arecord {i = List (Posed Bits8)}).encode (TLS12, (_ ** Handshake [(_ ** ClientHello client_hello_object)]))
  putStrLn $ "client hello: " <+> xxd b_client_hello
  _ <- send_bytes sock b_client_hello

  putStrLn $ "reading server hello"
  (b_server_response, (Right (Right (TLS12, MkDPair _ (Handshake [MkDPair _ (ServerHello server_hello)]))))) <- smart_read {i = List (Posed Bits8)} sock alert_or_arecord.decode
  | (b_server_response, server_response) => putStrLn $ "unexpected server response: " <+> show server_response
  putStrLn $ "server hello: " <+> show server_hello

  let TLS_AES_128_GCM_SHA256 = cipher_suite server_hello
  | other => putStrLn $ "unexpected cipher suite: " <+> (show other)

  let TLS13 = get_server_version server_hello
  | other => putStrLn $ "unexpected TLS version: " <+> (show other)
  let Right (X25519, server_pk) = get_server_handshake_key server_hello
  | other => putStrLn $ "Server key: " <+> (show other)

  let digest = init Sha256
  let digest = update (drop 5 b_client_hello) digest
  let digest = update (drop 5 b_server_response) digest

  let (Just shared_secret) = do
    pk <- deserialize_pk {a=X25519_DH} server_pk
    diffie_hellman {a=X25519_DH} sk pk

  putStrLn $ "shared secret: " <+> (xxd shared_secret)

  let hsk@(MkHandshakeKeys _ c_hs_k s_hs_k c_hs_iv s_hs_iv c_tr_key s_tr_key) =
    tls13_handshake_derive Sha256 12 16 shared_secret (toList $ finalize digest)

  putStrLn "key exchange calc"
  putStrLn $ "server_traffic_secret: " <+> (xxd $ toList c_tr_key)
  putStrLn $ "client_traffic_secret: " <+> (xxd $ toList s_tr_key)

  putStrLn "read change cipher spec"
  (b_server_response, (Right (Right (_, MkDPair _ (ChangeCipherSpec [0x01]))))) <- smart_read {i = List (Posed Bits8)} sock alert_or_arecord.decode
  | (b_server_response, server_response) => putStrLn $ "unexpected server response: " <+> show server_response

  putStrLn "read more encrypted server handshake messages"

  (b_application_data, Right (Right (_, MkDPair _ (ApplicationData application_data)))) <- smart_read {i = List (Posed Bits8)} sock $ alert_or_arecord.decode
  | (b_application_data, server_response) => putStrLn $ "unexpected server response: " <+> show server_response

  let Just wrapper = from_application_data {mac_size = 16} application_data
  | Nothing => putStrLn $ "malformed wrapper: " <+> xxd application_data

  putStrLn $ "decrypting data"
  let (plaintext, True) = decrypt {a=AES_128_GCM} s_hs_k s_hs_iv wrapper.encrypted_data (take 5 b_application_data) (toList wrapper.auth_tag)
  | (plaintext, False) => putStrLn "mac verification failed"
  putStrLn $ "plaintext: " <+> xxd plaintext

  -- putStrLn $ "send change cipher spec"
  -- _ <- send_bytes sock $ (arecord {i = List (Posed Bits8)}).encode (TLS12, MkDPair _ (ChangeCipherSpec [0x01]))

  let digest = update (init' plaintext) digest
  let (MkApplicationKeys c_ap_k s_ap_k c_ap_iv s_ap_iv) = tls13_application_derive Sha256 hsk (toList $ finalize digest)

  let client_verify_data = tls13_verify_data Sha256 c_tr_key $ toList $ finalize digest
  let client_handshake_finished = to_application_data $ MkWrappedRecord Handshake ((with_id no_id_finished).encode {i = List (Posed Bits8)} $ Finished $ MkFinished client_verify_data)
  let record_length = (length client_handshake_finished) + 16 -- 16 because AES_128_GCM
  let b_record = record_type_with_version_with_length.encode {i = List (Posed Bits8)} (ApplicationData, TLS12, record_length)

  let (chf_encrypted, chf_mac_tag) = encrypt {a=AES_128_GCM} c_hs_k c_hs_iv client_handshake_finished b_record

  let b_chf_wrapped = (arecord {i = List (Posed Bits8)}).encode (TLS12, MkDPair _ (ApplicationData $ to_application_data $ MkWrapper chf_encrypted chf_mac_tag))

  putStrLn $ "ap key exchange"
  putStrLn $ "c_hs_k: " <+> (xxd $ toList c_hs_k)
  putStrLn $ "c_hs_iv: " <+> (xxd $ toList c_hs_iv)
  putStrLn $ "c_ap_k: " <+> (xxd $ toList c_ap_k)
  putStrLn $ "c_ap_iv: " <+> (xxd $ toList c_ap_iv)
  putStrLn $ "s_ap_k: " <+> (xxd $ toList s_ap_k)
  putStrLn $ "s_ap_iv: " <+> (xxd $ toList s_ap_iv)

  putStrLn $ "sending client handshake finished"
  _ <- send_bytes sock b_chf_wrapped

  putStrLn $ "client_handshake_finished: " <+> xxd client_handshake_finished
  putStrLn $ "chf_encrypted: " <+> xxd chf_encrypted
  putStrLn $ "chf_mac_tag: " <+> (xxd $ toList chf_mac_tag)
  putStrLn $ "client_verify_data: " <+> xxd client_verify_data
  putStrLn $ "b_chf_wrapped: " <+> xxd b_chf_wrapped

  putStrLn $ "client handshake finished sent"

  let b_application_data = to_application_data $ MkWrappedRecord ApplicationData (encode_ascii $ test_http_body target_hostname)
  let record_length = (length b_application_data) + 16 -- 16 because AES_128_GCM
  let b_record_header = (record_type_with_version_with_length {i = List (Posed Bits8)}).encode (ApplicationData, TLS12, record_length)
  let (app_encrypted, app_mac_tag) = encrypt {a=AES_128_GCM} c_ap_k c_ap_iv b_application_data b_record_header
  let b_app_wrapped = arecord.encode {i = List (Posed Bits8)} (TLS12, MkDPair _ (ApplicationData $ to_application_data $ MkWrapper app_encrypted app_mac_tag))
  _ <- send_bytes sock b_app_wrapped

  putStrLn $ "https sent"
  putStrLn $ "app_encrypted: " <+> xxd app_encrypted
  putStrLn $ "app_mac_tag: " <+> (xxd $ toList app_mac_tag)
  putStrLn $ "length app_encrypted: " <+> (show $ length app_encrypted)
  putStrLn $ "length app_mac_tag: " <+> (show $ length $ toList app_mac_tag)
  putStrLn $ "b_application_data: " <+> xxd b_application_data
  putStrLn $ "b_record_header: " <+> xxd b_record_header
  putStrLn $ "b_app_wrapped: " <+> xxd b_app_wrapped

  (b_application_data, Right (Right (_, MkDPair _ (ApplicationData application_data)))) <- smart_read {i = List (Posed Bits8)} sock $ alert_or_arecord.decode
  | (b_application_data, server_response) => putStrLn $ "unexpected server response: " <+> show server_response

  let Just wrapper = from_application_data {mac_size = 16} application_data
  | Nothing => putStrLn $ "malformed wrapper: " <+> xxd application_data
  let server_wrapper_decrypted = 0
  let s_ap_iv = zipWith xor s_ap_iv (integer_to_be _ server_wrapper_decrypted)
  let (plaintext, True) = decrypt {a=AES_128_GCM} s_ap_k s_ap_iv wrapper.encrypted_data (take 5 b_application_data) (toList wrapper.auth_tag)
  | (plaintext, False) => putStrLn "mac verification failed"

  putStrLn $ "vvvvvvv http response vvvvvvvv"
  putStrLn $ xxd plaintext
  putStrLn $ show $ utf8_decode plaintext
