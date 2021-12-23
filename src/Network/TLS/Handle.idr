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

import Control.Linear.LIO

public export
tls_version_to_state_type : TLSVersion -> Type
tls_version_to_state_type TLS12 = TLSState Application2
tls_version_to_state_type TLS13 = TLSState Application3
tls_version_to_state_type _ = Void

export
record TLSHandle (tls_version : TLSVersion) t_ok t_closed where
  constructor MkTLSHandle
  1 handle : Handle t_ok t_closed (Res String $ \_ => t_closed) (Res String $ \_ => t_closed)
  state : tls_version_to_state_type tls_version
  buffer : List Bits8

public export
OkOrError : TLSVersion -> Type -> Type -> Type
OkOrError tls_version t_ok t_closed = Res Bool $ \ok => if ok then TLSHandle tls_version t_ok t_closed else Res String (\_ => t_closed)

public export
UnderlyingHandle : Type -> Type -> Type
UnderlyingHandle t_ok t_closed = Handle t_ok t_closed (Res String $ \_ => t_closed) (Res String $ \_ => t_closed)

read_record : LinearIO m => (1 _ : UnderlyingHandle t_ok t_closed) -> L1 m $ Res Bool $ \ok => if ok
  then Res (List Bits8) (\_ => UnderlyingHandle t_ok t_closed)
  else Res String (\_ => t_closed)
read_record handle = do
  -- read header
  (True # (b_header # handle)) <- read handle 5
  | (False # (error # handle)) => pure1 (False # ("recv_byte (record header / alert) failed" <+> error # handle))
  let (Pure [] (Right (_, TLS12, len))) =
    feed {i = List (Posed Bits8)} (map (uncurry MkPosed) $ enumerate 0 b_header) (alert <|> record_type_with_version_with_length).decode
  | Pure [] (Left x) => (close handle) >>= (\s => pure1 (False # (("ALERT: " <+> show x) # s)))
  | _ => (close handle) >>= (\s => pure1 (False # (("unable to parse header: " <+> xxd b_header) # s)))

  -- read record content
  (True # (b_body # handle)) <- read handle (cast len)
  | (False # (error # handle)) => pure1 (False # ("recv_byte (record body) failed: " <+> error # handle))
  if length b_body == cast len
    then pure1 (True # (b_header <+> b_body # handle))
    else let err =
             "length does not match header: "
               <+> xxd b_body
               <+> "\nexpected length: "
               <+> show len
               <+> "\nactual length: "
               <+> (show $ length b_body)
         in (close handle) >>= (\s => pure1 (False # (err # s)))

gen_key : MonadRandom m => (g : SupportedGroup) ->
                           m (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))
gen_key group = do
  keypair <- generate_key_pair @{snd $ curve_group_to_type group}
  pure (group ** keypair)

tls2_handshake : LinearIO io => TLSState ServerHello2 ->
                 (1 _ : UnderlyingHandle t_ok t_closed) ->
                 CertificateCheck IO ->
                 L1 io (OkOrError TLS12 t_ok t_closed)
tls2_handshake state handle cert_ok = do
  (True # (b_cert # handle)) <- read_record handle
  | (False # other) => pure1 (False # other)

  Right state <- liftIO1 $ serverhello2_to_servercert state b_cert cert_ok
  | Left error => (close handle) >>= (\s => pure1 (False # (error # s)))

  (True # (b_skex # handle)) <- read_record handle
  | (False # other) => pure1 (False # other)

  let Right state = servercert_to_serverkex state b_skex
  | Left error => (close handle) >>= (\s => pure1 (False # (error # s)))

  (True # (b_s_hello_done # handle)) <- read_record handle
  | (False # other) => pure1 (False # other)

  let Right (state, handshake_data) = serverkex_process_serverhellodone state b_s_hello_done
  | Left error => (close handle) >>= (\s => pure1 (False # (error # s)))

  (True # handle) <- write handle handshake_data
  | (False # (error # handle)) => pure1 (False # ("send_byte (handshake data) failed: " <+> error # handle))

  (True # (b_ccs # handle)) <- read_record handle
  | (False # other) => pure1 (False # other)

  let Right state = serverhellodone_to_applicationready2 state b_ccs
  | Left error => (close handle) >>= (\s => pure1 (False # (error # s)))

  (True # (b_fin # handle)) <- read_record handle
  | (False # other) => pure1 (False # other)

  case applicationready2_to_application2 state b_fin of
    Right state => pure1 (True # MkTLSHandle handle state [])
    Left error => (close handle) >>= (\s => pure1 (False # (error # s)))

tls3_handshake : LinearIO io => TLSState ServerHello3 ->
                 (1 _ : UnderlyingHandle t_ok t_closed) ->
                 CertificateCheck IO ->
                 L1 io (OkOrError TLS13 t_ok t_closed)
tls3_handshake state handle cert_ok = do
  (True # (b_response # handle)) <- read_record handle
  | (False # other) => pure1 (False # other)
  parsed <- liftIO1 $ tls3_serverhello_to_application state b_response cert_ok
  case parsed of
    Right (Right (client_verify, state)) => do
      (True # handle) <- write handle client_verify
      | (False # (error # handle)) => pure1 (False # ("send_byte (client verify data) failed: " <+> error # handle))
      pure1 (True # MkTLSHandle handle state [])
    Right (Left state) =>
      tls3_handshake state handle cert_ok
    Left error =>
      (close handle) >>= (\s => pure1 (False # (error # s)))

export
tls_handshake : (MonadRandom IO, LinearIO io) => String ->
                (1 _ : UnderlyingHandle t_ok t_closed) ->
                CertificateCheck IO ->
                L1 io (Res Bool $ \ok => if ok then Res TLSVersion (\tls_version => TLSHandle tls_version t_ok t_closed) else Res String (\_ => t_closed))
tls_handshake target_hostname handle cert_ok = do
  random <- liftIO1 $ random_bytes _
  keypairs <- liftIO1 $ traverse gen_key (X25519 ::: [ SECP256r1, SECP384r1 ])
  let
    (client_hello, state) =
      tls_init_to_clienthello $ TLS_Init $ MkTLSInitialState
        target_hostname
        random
        []
        (tls13_supported_cipher_suites <+> tls12_supported_cipher_suites)
        (RSA_PKCS1_SHA256 ::: [RSA_PSS_RSAE_SHA256, ECDSA_SECP256r1_SHA256])
        keypairs

  (True # handle) <- write handle client_hello
  | (False # (error # handle)) => pure1 (False # ("send client_hello failed: " <+> error # handle))

  (True # (b_server_hello # handle)) <- read_record handle
  | (False # other) => pure1 (False # other)

  case tls_clienthello_to_serverhello state b_server_hello of
    Right (Right state) => do
      (True # ok) <- tls3_handshake state handle cert_ok
      | (False # no) => pure1 (False # no)
      pure1 (True # (TLS13 # ok))
    Right (Left state) => do
      (True # ok) <- tls2_handshake state handle cert_ok
      | (False # no) => pure1 (False # no)
      pure1 (True # (TLS12 # ok))
    Left error => (close handle) >>= (\s => pure1 (False # (error # s)))
