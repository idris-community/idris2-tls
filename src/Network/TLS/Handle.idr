module Network.TLS.Handle

import Control.Monad.Error.Either
import Control.Monad.State
import Crypto.ECDH
import Crypto.Random
import Data.List1
import Data.Vect
import Network.TLS.Core
import Network.TLS.Magic
import Network.TLS.Parsing
import Network.TLS.Record
import Utils.Bytes
import Utils.Handle
import Utils.Misc
import Utils.Parser

read_record : Monad m => Handle m -> EitherT String m (List Bits8)
read_record handle = do
  (_ ** (_, b_header)) <- handle.read 5
  let (Pure [] (Right (_, TLS12, len))) = 
    feed {i = List (Posed Bits8)} (map (uncurry MkPosed) $ enumerate 0 $ toList b_header) (alert <|> record_type_with_version_with_length).decode
  | Pure [] (Left x) => throwE $ "ALERT: " <+> show x
  | _ => throwE "unable to parse header"
  (_ ** (_, b_body)) <- handle.read (cast len)
  case length b_body == cast len of
    False => throwE $ "length does not match header: " <+> (xxd $ toList b_body)
    True => pure $ (toList b_header) <+> (toList b_body)

gen_key : MonadRandom m => (g : SupportedGroup) -> m (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))
gen_key group = do
  keypair <- generate_key_pair @{snd $ curve_group_to_type group}
  pure (group ** keypair)

handshake : Monad m => (Certificate -> m Bool) -> Handle m -> TLSState ServerHello3 -> EitherT String m (TLSState Application3)
handshake cert_check handle state = do
  response <- read_record handle
  parsed <- tls3_serverhello_to_application state response (MkEitherT . map Right . cert_check)
  case parsed of
    Right (Right (client_verify, state)) => (handle.write client_verify) *> (pure state)
    Right (Left (state)) => handshake cert_check handle state
    Left err => throwE err

record TLSHandleState where
  constructor MkTLSHandleState
  tls : TLSState Application3
  buffer : List Bits8

public export
tls_wrap_handle : (MonadRandom m, HasIO m) => (Certificate -> m Bool) -> String -> Handle m -> EitherT String m (Handle m)
tls_wrap_handle cert_check hostname handle = do
  keys <- MkEitherT $ map Right $ traverse gen_key (X25519 ::: [ SECP256r1 ])
  random <- MkEitherT $ map Right $ random_bytes _
  let
    init_state =
      MkTLSInitialState hostname random []
        (TLS_AES_128_GCM_SHA256 ::: [ TLS_AES_256_GCM_SHA384, TLS_CHACHA20_POLY1305_SHA256 ])
        (RSA_PKCS1_SHA256 ::: [RSA_PSS_RSAE_SHA256, ECDSA_SECP256r1_SHA256])
        keys
  
  --- Client Hello
  let (client_hello, state) = tls_init_to_clienthello $ TLS_Init init_state
  handle.write client_hello

  --- Server Hello
  b_server_hello <- read_record handle
  Right state <- MkEitherT $ pure $ tls_clienthello_to_serverhello state b_server_hello
  | Left state => throwE "TLS 1.2 not supported"

  --- Handshake Key Exchange
  state <- handshake cert_check handle state

  let handle_state = MkTLSHandleState state []
  pure $ MkHandle ?a ?b
