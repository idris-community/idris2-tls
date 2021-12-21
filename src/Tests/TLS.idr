module Tests.TLS

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
import Utils.Network.C
import Utils.Parser

-- Needed for big record
-- or not? I added a putStrLn and it only printed once
-- but if I just use recv_bytes it would only read 4006 bytes instead of 4580
-- tested on www.hkust.edu.hk:443
-- TODO: find out what the hell is happening here
recv_n_bytes : HasIO m => Socket -> Nat -> List Bits8 -> m (Maybe (List Bits8))
recv_n_bytes sock size buf = do
  Just response <- recv_bytes sock $ cast $ minus size $ length buf
  | Nothing => pure Nothing
  let buf = buf <+> response
  if (length buf) >= size 
    then pure $ Just buf
    else recv_n_bytes sock size buf

read_record : HasIO m => Socket -> m (Either String (List Bits8))
read_record sock = do
  Just b_header <- recv_bytes sock 5
  | Nothing => pure $ Left "recv_byte (record header / alert) failed"
  let (Pure [] (Right (_, TLS12, len))) = 
    feed {i = List (Posed Bits8)} (map (uncurry MkPosed) $ enumerate 0 b_header) (alert <|> record_type_with_version_with_length).decode
  | Pure [] (Left x) => pure $ Left $ "ALERT: " <+> show x
  | _ => pure $ Left $ "unable to parse header: " <+> xxd b_header
  Just b_body <- recv_n_bytes sock (cast len) []
  | Nothing => pure $ Left "recv_byte (record body) failed"
  case length b_body == cast len of
    False => 
      pure 
      $ Left 
      $ "length does not match header: " 
      <+> xxd b_body 
      <+> "\nexpected length: " 
      <+> show len 
      <+> "\nactual length: " 
      <+> (show $ length b_body)
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

gen_key : MonadRandom m => (g : SupportedGroup) -> m (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))
gen_key group = do
  keypair <- generate_key_pair @{snd $ curve_group_to_type group}
  pure (group ** keypair)

tls2_test : HasIO m => Socket -> (target_hostname : String) -> TLSState ServerHello2 -> m ()
tls2_test sock target_hostname state = do
  putStrLn "tls/1.2 detected"

  Right b_cert <- read_record sock
  | Left err => putStrLn err

  putStrLn "parsing certificate"
  let Right state = serverhello2_to_servercert state b_cert
  | Left err => putStrLn err

  Right b_skex <- read_record sock
  | Left err => putStrLn err

  putStrLn "kex"
  let Right state = servercert_to_serverkex state b_skex
  | Left err => putStrLn err

  Right b_s_hello_done <- read_record sock
  | Left err => putStrLn err

  putStrLn "server hello done"
  let Right (state, handshake_data) = serverkex_process_serverhellodone state b_s_hello_done
  | Left err => putStrLn err

  _ <- send_bytes sock handshake_data

  putStrLn "change cipher spec"
  Right b_ccs <- read_record sock
  | Left err => putStrLn err

  let Right state = serverhellodone_to_applicationready2 state b_ccs
  | Left err => putStrLn err

  putStrLn "server finished"
  Right b_fin <- read_record sock
  | Left err => putStrLn err

  let Right state = applicationready2_to_application2 state b_fin
  | Left err => putStrLn err

  putStrLn "sending application data"
  let (state, wrapper) = encrypt_to_record2 state (encode_ascii $ test_http_body target_hostname)
  _ <- send_bytes sock wrapper

  Right b_response <- read_record sock
  | Left err => putStrLn err

  let Right (state, plaintext) = decrypt_from_record2 state b_response
  | Left err => putStrLn err

  putStrLn $ "vvvvvvv http response vvvvvvvv"
  putStrLn $ xxd plaintext
  putStrLn $ show $ utf8_decode plaintext

  putStrLn "ok tls/1.2"

tls3_test : HasIO m => Socket -> (target_hostname : String) -> TLSState ServerHello3 -> m ()
tls3_test sock target_hostname state = do
  putStrLn "tls/1.3 detected"

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

  putStrLn "ok tls/1.3"

tls_test : HasIO m => (target_hostname : String) -> Int -> m ()
tls_test target_hostname port = do
  Right sock <- socket AF_INET Stream 0
  | Left err => putStrLn $ "unable to create socket: " <+> show err

  putStrLn "genreating keys"
  keys <- traverse gen_key (X25519 ::: [ SECP256r1 ])
  random <- random_bytes _
  putStrLn "done"

  let
    init_state =
      MkTLSInitialState
        target_hostname
        random
        []
        (TLS_AES_128_GCM_SHA256 ::: [ TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256, TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 ])
        (RSA_PKCS1_SHA256 ::: [RSA_PSS_RSAE_SHA256, ECDSA_SECP256r1_SHA256])
        keys

  putStrLn $ "connecting to " <+> target_hostname
  0 <- connect sock (Hostname target_hostname) port
  | _ => putStrLn $ "unable to connect"
  putStrLn $ "connected"

  let (client_hello, state) = tls_init_to_clienthello $ TLS_Init init_state
  _ <- send_bytes sock client_hello

  Right b_server_hello <- read_record sock
  | Left err => putStrLn err

  putStrLn "server_hello:"
  putStrLn $ xxd b_server_hello

  case tls_clienthello_to_serverhello state b_server_hello of
    Right (Right state) => tls3_test sock target_hostname state
    Right (Left state) => tls2_test sock target_hostname state
    Left err => putStrLn err
