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
import Control.Monad.Error.Either

liftM : Monad m => m a -> EitherT e m a
liftM = MkEitherT . map Right

liftE : Monad m => Either e a -> EitherT e m a
liftE = MkEitherT . pure

log : HasIO io => String -> EitherT e io ()
log = liftM . putStrLn

read_record : HasIO m => Socket -> EitherT String m (List Bits8)
read_record sock = MkEitherT $ do
  Just b_header <- recv_bytes sock 5
  | Nothing => pure $ Left "recv_byte (record header / alert) failed"
  let (Pure [] (Right (_, TLS12, len))) = 
    feed {i = List (Posed Bits8)} (map (uncurry MkPosed) $ enumerate 0 b_header) (alert <|> record_type_with_version_with_length).decode
  | Pure [] (Left x) => pure $ Left $ "ALERT: " <+> show x
  | _ => pure $ Left $ "unable to parse header: " <+> xxd b_header
  Just b_body <- recv_bytes sock (cast len)
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

--- TODO: this
certificate_check : HasIO io => CertificateCheck io
certificate_check certficiate = pure True

gen_key : MonadRandom m => (g : SupportedGroup) -> m (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))
gen_key group = do
  keypair <- generate_key_pair @{snd $ curve_group_to_type group}
  pure (group ** keypair)

tls2_test : HasIO m => Socket -> (target_hostname : String) -> TLSState ServerHello2 -> EitherT String m ()
tls2_test sock target_hostname state = do
  log "tls/1.2 detected"
  b_cert <- read_record sock

  log "parsing certificate"
  state <- MkEitherT $ serverhello2_to_servercert state b_cert certificate_check

  b_skex <- read_record sock

  log "kex"
  state <- liftE $ servercert_to_serverkex state b_skex

  b_s_hello_done <- read_record sock

  log "server hello done"
  (state, handshake_data) <- liftE $ serverkex_process_serverhellodone state b_s_hello_done

  _ <- liftM $ send_bytes sock handshake_data

  log "change cipher spec"
  b_ccs <- read_record sock

  state <- liftE $ serverhellodone_to_applicationready2 state b_ccs

  log "server finished"
  b_fin <- read_record sock

  state <- liftE $ applicationready2_to_application2 state b_fin

  log "sending application data"
  let (state, wrapper) = encrypt_to_record2 state (encode_ascii $ test_http_body target_hostname)
  _ <- liftM $ send_bytes sock wrapper

  b_response <- read_record sock

  (state, plaintext) <- liftE $ decrypt_from_record2 state b_response

  log "vvvvvvv http response vvvvvvvv"
  log $ xxd plaintext
  log $ show $ utf8_decode plaintext

  log "ok tls/1.2"

handshake : HasIO io => Socket -> TLSState ServerHello3 -> EitherT String io (TLSState Application3)
handshake sock state = do
  response <- read_record sock
  parsed <- MkEitherT $ tls3_serverhello_to_application state response certificate_check
  case parsed of
    Right (client_verify, state) => (liftM $ send_bytes sock client_verify) *> (pure state)
    Left state => handshake sock state

tls3_test : HasIO m => Socket -> (target_hostname : String) -> TLSState ServerHello3 -> EitherT String m ()
tls3_test sock target_hostname state = do
  log "tls/1.3 detected"
  log "perform handshake"
  state <- handshake sock state

  let (state, wrapper) = encrypt_to_record state (encode_ascii $ test_http_body target_hostname)

  log "wrapper:"
  log $ xxd wrapper

  _ <- liftM $ send_bytes sock wrapper

  b_response <- read_record sock

  (state, plaintext) <- liftE $ decrypt_from_record state b_response

  log "vvvvvvv http response vvvvvvvv"
  log $ xxd plaintext
  log $ show $ utf8_decode plaintext

  b_response <- read_record sock
  (state, plaintext) <- liftE $ decrypt_from_record state b_response

  log "vvvvvvv http response vvvvvvvv"
  log $ xxd plaintext
  log $ show $ utf8_decode plaintext

  b_response <- read_record sock
  (state, plaintext) <- liftE $ decrypt_from_record state b_response

  log "vvvvvvv http response vvvvvvvv"
  log $ xxd plaintext
  log $ show $ utf8_decode plaintext

  log "ok tls/1.3"

tls_test' : HasIO m => List1 (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g))) ->
            (target_hostname : String) -> Int -> EitherT String m ()
tls_test' keypairs target_hostname port = do
  sock <- bimapEitherT (\err => "unable to create socket: " <+> show err) id
    $ MkEitherT 
    $ socket AF_INET Stream 0

  random <- liftM $ random_bytes _

  let
    init_state =
      MkTLSInitialState
        target_hostname
        random
        []
        (tls13_supported_cipher_suites <+> tls12_supported_cipher_suites)
        (RSA_PKCS1_SHA256 ::: [RSA_PSS_RSAE_SHA256, ECDSA_SECP256r1_SHA256])
        keypairs

  log $ "connecting to " <+> target_hostname
  0 <- liftM $ connect sock (Hostname target_hostname) port
  | _ => throwE "unable to connect"
  log "connected"

  let (client_hello, state) = tls_init_to_clienthello $ TLS_Init init_state
  _ <- liftM $ send_bytes sock client_hello

  b_server_hello <- read_record sock

  log "server_hello:"
  log $ xxd b_server_hello

  tls_state <- liftE $ tls_clienthello_to_serverhello state b_server_hello

  case tls_state of
    Right state => tls3_test sock target_hostname state
    Left state => tls2_test sock target_hostname state

tls_test : HasIO m => (target_hostname : String) -> Int -> m ()
tls_test target_hostname port = do
  putStrLn "genreating keys"
  keys <- traverse gen_key (X25519 ::: [ SECP256r1, SECP384r1 ])
  putStrLn "done"
  Right () <- runEitherT $ tls_test' keys target_hostname port
  | Left err => putStrLn err
  pure ()
