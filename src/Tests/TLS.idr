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

read_record : HasIO m => Socket -> m (Either String (List Bits8))
read_record sock = do
  Just b_header <- recv_bytes sock 5
  | Nothing => pure $ Left "recv_byte (record header / alert) failed"
  let (Pure [] (Right (_, TLS12, len))) = feed {i = List (Posed Bits8)} (map (uncurry MkPosed) $ enumerate 0 b_header) (alert <|> record_type_with_version_with_length).decode
  | Pure [] (Left x) => pure $ Left $ "ALERT: " <+> show x
  | _ => pure $ Left $ "unable to parse header"
  Just b_body <- recv_bytes sock (cast len)
  | Nothing => pure $ Left "recv_byte (record body) failed"
  case length b_body == cast len of
    False => pure $ Left $ "length does not match header: " <+> xxd b_body
    True => pure $ Right $ b_header <+> b_body

test_http_body : String -> String
test_http_body hostname = "GET / HTTP/1.1\nHost: " <+> hostname <+> "\n\n"

example_hostname : String
example_hostname = "www.cloudflare.com"

handshake : HasIO io => Socket -> TLSState ServerHello3 -> io (Either String (TLSState Application3))
handshake sock state = do
  Right response <- read_record sock
  | Left err => pure $ Left err
  parsed <- tls3_serverhello_to_application state response (const $ pure True)
  case parsed of
    Right (Right (client_verify, state)) => (send_bytes sock client_verify) *> (pure $ Right state)
    Right (Left (state)) => handshake sock state
    Left err => pure $ Left err

partial
tls_test : HasIO m => (target_hostname : String) -> m ()
tls_test target_hostname = do
  Right sock <- socket AF_INET Stream 0
  | Left err => putStrLn $ "unable to create socket: " <+> show err

  putStrLn $ "generate key pair"
  -- (sk, pk) <- generate_key_pair
  let sk = the (Vect 32 Bits8) $
    [ 0xcc, 0x93, 0x5d, 0xb7, 0x60, 0x54, 0xe7, 0x2d, 0x3a, 0x29, 0xcb, 0x62, 0x5d, 0xc0, 0x10, 0xca, 0x6d
    , 0x46, 0x0e, 0xf6, 0x56, 0xf5, 0x06, 0xa5, 0xbb, 0x50, 0x4a, 0xb0, 0x68, 0x28, 0x34, 0x30]
  let pk = the (Vect 32 Bits8) $
    [ 0x38, 0xf3, 0xa1, 0xf3, 0xa8, 0x3b, 0x6c, 0x55, 0x88, 0x9a, 0x4b, 0x5d, 0x62, 0x81, 0x70, 0xf5, 0xe6
    , 0xca, 0x09, 0x60, 0xb9, 0x3b, 0x4a, 0xd8, 0x95, 0x59, 0x00, 0x2d, 0x72, 0x78, 0x9d, 0x24 ]

  let
    init_state =
      MkTLSInitalState
        target_hostname
        (map (cast . finToNat) range)
        []
        (TLS_AES_128_GCM_SHA256 ::: [ TLS_AES_256_GCM_SHA384, TLS_CHACHA20_POLY1305_SHA256 ])
        (RSA_PKCS1_SHA256 ::: [RSA_PSS_RSAE_SHA256, ECDSA_SECP256r1_SHA256])
        (singleton (X25519 ** (sk, pk)))

  putStrLn $ "connecting to " <+> target_hostname
  0 <- connect sock (Hostname target_hostname) 443
  | _ => putStrLn $ "unable to connect"
  putStrLn $ "connected"

  let (client_hello, state) = tls_init_to_clienthello $ TLS_Init init_state
  _ <- send_bytes sock client_hello

  Right b_server_hello <- read_record sock
  | Left err => putStrLn err

  putStrLn "server_hello:"
  putStrLn $ xxd b_server_hello

  let Right (Right state) = tls_clienthello_to_serverhello state b_server_hello
  | Right (Left _) => putStrLn "TLS 1.2 not supported"
  | Left err => putStrLn err

  putStrLn "perform handshake"
  Right state <- handshake sock state
  | Left err => putStrLn err

  let (state, wrapper) = encrypt_to_record state (encode_ascii $ test_http_body target_hostname)

  putStrLn "wrapper:"
  putStrLn $ xxd wrapper

  _ <- send_bytes sock wrapper

  Right b_response <- read_record sock
  | Left err => putStrLn err

  let Right (state, plaintext) = decrypt_from_record state b_response
  | Left err => putStrLn err

  putStrLn $ "vvvvvvv http response vvvvvvvv"
  putStrLn $ xxd plaintext
  putStrLn $ show $ utf8_decode plaintext

  Right b_response <- read_record sock
  | Left err => putStrLn err

  let Right (state, plaintext) = decrypt_from_record state b_response
  | Left err => putStrLn err

  putStrLn $ "vvvvvvv http response vvvvvvvv"
  putStrLn $ xxd plaintext
  putStrLn $ show $ utf8_decode plaintext

  Right b_response <- read_record sock
  | Left err => putStrLn err

  let Right (state, plaintext) = decrypt_from_record state b_response
  | Left err => putStrLn err

  putStrLn $ "vvvvvvv http response vvvvvvvv"
  putStrLn $ xxd plaintext
  putStrLn $ show $ utf8_decode plaintext

  putStrLn "ok"
