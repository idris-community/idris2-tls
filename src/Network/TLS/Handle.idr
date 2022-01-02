module Network.TLS.Handle

import Control.Linear.LIO
import Control.Monad.Error.Either
import Control.Monad.State
import Crypto.ECDH
import Crypto.Random
import Data.List
import Data.List1
import Data.Vect
import Data.Void
import Network.TLS.Core
import Network.TLS.Magic
import Network.TLS.Parsing
import Network.TLS.Record
import Utils.Bytes
import Utils.Handle
import Utils.Misc
import Utils.Parser

public export
tls_version_to_state_type : TLSVersion -> Type
tls_version_to_state_type TLS12 = TLSState Application2
tls_version_to_state_type TLS13 = TLSState Application3
tls_version_to_state_type _ = Void

export
record TLSHandle (version : TLSVersion) t_ok t_closed where
  constructor MkTLSHandle
  1 handle : Handle t_ok t_closed (Res String $ const t_closed) (Res String $ const t_closed)
  state : tls_version_to_state_type version
  buffer : List Bits8

public export
Uninhabited (TLSHandle TLS10 t_ok t_closed) where
  uninhabited = state

public export
Uninhabited (TLSHandle TLS11 t_ok t_closed) where
  uninhabited = state

OkOrError : TLSVersion -> Type -> Type -> Type
OkOrError tls_version t_ok t_closed = Res Bool $ \ok => if ok then TLSHandle tls_version t_ok t_closed else Res String (const t_closed)

public export
Handle' : Type -> Type -> Type
Handle' t_ok t_closed = Handle t_ok t_closed (Res String $ const t_closed) (Res String $ const t_closed)

read_record : LinearIO m => (1 _ : Handle' t_ok t_closed) -> L1 m $ Res Bool $ \ok => if ok then Res (List Bits8) (const $ Handle' t_ok t_closed) else Res String (const t_closed)
read_record handle = do
  -- read header
  (True # (b_header # handle)) <- read handle 5
  | (False # (error # handle)) => pure1 (False # ("read (record header / alert) failed" <+> error # handle))
  let (Pure [] (Right (_, TLS12, len))) =
    feed {i = List (Posed Bits8)} (map (uncurry MkPosed) $ enumerate 0 b_header) (alert <|> record_type_with_version_with_length).decode
  | Pure [] (Left x) => (close handle) >>= (\s => pure1 (False # (("ALERT: " <+> show x) # s)))
  | _ => (close handle) >>= (\s => pure1 (False # (("unable to parse header: " <+> xxd b_header) # s)))

  -- read record content
  (True # (b_body # handle)) <- read handle (cast len)
  | (False # (error # handle)) => pure1 (False # ("read (record body) failed: " <+> error # handle))
  if length b_body == cast len
    then pure1 (True # (b_header <+> b_body # handle))
    else let err = "length does not match header: " <+> xxd b_body
               <+> "\nexpected length: " <+> show len
               <+> "\nactual length: " <+> (show $ length b_body)
         in (close handle) >>= (\s => pure1 (False # (err # s)))

gen_key : MonadRandom m => (g : SupportedGroup) -> m (DPair SupportedGroup (\g => Pair (curve_group_to_scalar_type g) (curve_group_to_element_type g)))
gen_key group = do
  keypair <- generate_key_pair @{snd $ curve_group_to_type group}
  pure (group ** keypair)

tls2_handshake : LinearIO io => TLSState ServerHello2 -> (1 _ : Handle' t_ok t_closed) -> CertificateCheck IO -> L1 io (OkOrError TLS12 t_ok t_closed)
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

tls3_handshake : LinearIO io => TLSState ServerHello3 -> (1 _ : Handle' t_ok t_closed) -> CertificateCheck IO -> L1 io (OkOrError TLS13 t_ok t_closed)
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

DecryptFunction : Type -> Type
DecryptFunction state = state -> List Bits8 -> Either String (state, List Bits8)

EncryptFunction : Type -> Type
EncryptFunction state = state -> List Bits8 -> (state, List Bits8)

tlshandle_read : {version : _} -> LinearIO io => (wanted : Nat) -> (1 _ : TLSHandle version t_ok t_closed) -> DecryptFunction (tls_version_to_state_type version) -> L1 io (Res Bool $ ReadHack (TLSHandle version t_ok t_closed) (Res String (const t_closed)))
tlshandle_read wanted (MkTLSHandle handle state buffer) decrypt =
  let (a, b) = splitAt wanted buffer
  in if (length a) == wanted
        then pure1 (True # (a # MkTLSHandle handle state b))
        else do
          (True # (b_record # handle)) <- read_record handle
          | (False # other) => pure1 (False # other)
          case decrypt state b_record of
            Right (state, plaintext) => tlshandle_read wanted (MkTLSHandle handle state $ buffer <+> plaintext) decrypt
            Left error => (close handle) >>= (\s => pure1 (False # (error # s)))

tlshandle_write : {tls_version : TLSVersion} -> LinearIO io => List (List Bits8) -> (1 _ : TLSHandle tls_version t_ok t_closed) -> EncryptFunction (tls_version_to_state_type tls_version) -> L1 io (Res Bool $ WriteHack (TLSHandle tls_version t_ok t_closed) (Res String (const t_closed)))
tlshandle_write [] sock encrypt = pure1 (True # sock)
tlshandle_write (x :: xs) (MkTLSHandle handle state buffer) encrypt = do
  let (state, b_record) = encrypt state x
  (True # handle) <- write handle b_record
  | (False # (error # handle)) => pure1 (False # ("write (application data) failed: " <+> error # handle))
  tlshandle_write xs (MkTLSHandle handle state buffer) encrypt

||| Reference: OpenSSL
chunk_size : Nat
chunk_size = 0x2000

tlshandle_to_handle : {version : _} -> (1 _ : TLSHandle version t_ok t_closed) -> Handle' (TLSHandle version t_ok t_closed) t_closed
tlshandle_to_handle {version=TLS10} (MkTLSHandle handle state buffer) = (kill_linear state) handle
tlshandle_to_handle {version=TLS11} (MkTLSHandle handle state buffer) = (kill_linear state) handle
tlshandle_to_handle {version=TLS12} handle = MkHandle
  handle
  ( \sock, len => tlshandle_read len sock decrypt_from_record2 )
  ( \sock, input => tlshandle_write (chunk chunk_size input) sock encrypt_to_record2 )
  ( \(MkTLSHandle handle state buffer) => close handle )
tlshandle_to_handle {version=TLS13} handle = MkHandle
  handle
  ( \sock, len => tlshandle_read len sock decrypt_from_record )
  ( \sock, input => tlshandle_write (chunk chunk_size input) sock encrypt_to_record )
  ( \(MkTLSHandle handle state buffer) => close handle )

TLSHandle' : Type -> Type -> Type
TLSHandle' t_ok t_closed = Res TLSVersion $ \version => TLSHandle version t_ok t_closed

abstract_tlshandle : (1 _ : TLSHandle' t_ok t_closed) -> Handle' (TLSHandle' t_ok t_closed) t_closed
abstract_tlshandle x = MkHandle
  x
  ( \(v # h), wanted => do
      (True # (output # MkHandle h _ _ _)) <- read (tlshandle_to_handle h) wanted
      | (False # (err # x)) => pure1 $ False # (err # x)
      pure1 $ True # (output # (_ # h))
  )
  ( \(v # h), input => do
      (True # MkHandle h _ _ _) <- write (tlshandle_to_handle h) input
      | (False # (err # x)) => pure1 $ False # (err # x)
      pure1 $ True # (_ # h)
  )
  ( \(v # h) => close $ tlshandle_to_handle h
  )

export
tls_handshake : (MonadRandom IO, LinearIO io) => 
                String ->
                List1 SupportedGroup ->
                List1 SignatureAlgorithm ->
                List1 CipherSuite ->
                (1 _ : Handle' t_ok t_closed) ->
                CertificateCheck IO ->
                L1 io (Res Bool $ \ok => if ok then Handle' (TLSHandle' t_ok t_closed) t_closed else Res String (const t_closed))
tls_handshake target_hostname supported_groups signature_algos cipher_suites handle cert_ok = do
  random <- liftIO1 $ random_bytes _
  keypairs <- liftIO1 $ traverse gen_key supported_groups
  let
    (client_hello, state) =
      tls_init_to_clienthello $ TLS_Init $ MkTLSInitialState
        target_hostname
        random
        []
        cipher_suites
        signature_algos
        keypairs

  (True # handle) <- write handle client_hello
  | (False # (error # handle)) => pure1 (False # ("send client_hello failed: " <+> error # handle))

  (True # (b_server_hello # handle)) <- read_record handle
  | (False # other) => pure1 (False # other)

  case tls_clienthello_to_serverhello state b_server_hello of
    Right (Left state) => do
      (True # ok) <- tls2_handshake state handle cert_ok
      | (False # no) => pure1 (False # no)
      pure1 $ True # abstract_tlshandle (_ # ok)
    Right (Right state) => do
      (True # ok) <- tls3_handshake state handle cert_ok
      | (False # no) => pure1 (False # no)
      pure1 $ True # abstract_tlshandle (_ # ok)
    Left error => do
      h <- close handle
      pure1 $ False # (error # h)
