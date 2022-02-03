module CertTest

import Data.Vect
import Data.Fin
import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import System.Info
import System.FFI
import Data.Buffer
import Data.List
import Network.TLS.Certificate
import Network.TLS.Parse.PEM
import Data.String.Parser
import Data.Either
import System.File.Process
import System.File.ReadWrite
import System.Directory
import System

print_certificate : HasIO io => Either String Certificate -> io ()
print_certificate (Right cert) = printLn cert
print_certificate (Left err) = putStrLn "cannot parse: \{err}"

pem_to_certificate : PEMBlob -> Either String Certificate
pem_to_certificate (MkPEMBlob "CERTIFICATE" content) =
  bimap (\err => "error: \{err}, content:\n") id (parse_certificate content)
pem_to_certificate _ = Left "PEM is not a certificate"

--- START WINDOWS ---

%foreign "C:openCertStore,libidristls"
prim__open_cert_store : PrimIO AnyPtr

%foreign "C:closeCertStore,libidristls"
prim__close_cert_store : AnyPtr -> PrimIO Int

%foreign "C:nextCertInStore,libidristls"
prim__next_cert_in_store : AnyPtr -> AnyPtr -> PrimIO AnyPtr

%foreign "C:isNull, libidris2_support, idris_support.h"
prim__idrnet_isNull : (ptr : AnyPtr) -> PrimIO Int

%foreign "C:certLenInfo,libidristls"
prim__cert_len_info : AnyPtr -> PrimIO Int

%foreign "C:certBody,libidristls"
prim__cert_body : AnyPtr -> Buffer -> PrimIO ()

export
nullPtr : HasIO io => AnyPtr -> io Bool
nullPtr p = do
  i <- primIO $ prim__idrnet_isNull p
  pure (i /= 0)

buffer_to_list : HasIO io => Buffer -> io (List Bits8)
buffer_to_list buffer = rawSize buffer >>= \cap => traverse (getBits8 buffer) [0..(cap-1)]

test_windows_cert : EitherT String IO ()
test_windows_cert = do
  cert_store <- primIO prim__open_cert_store
  certs <- loop [] cert_store prim__getNullAnyPtr
  putStrLn "\{show (length certs)} certificates found"

  let certs_parsed = map parse_certificate certs
  traverse_ print_certificate certs_parsed

  b <- primIO $ prim__close_cert_store cert_store
  when (b == 0) (throwE "error occured while closing certificate store")
  where
    loop : HasIO io => List (List Bits8) -> AnyPtr -> AnyPtr -> io (List (List Bits8))
    loop acc cert_store prev_cert = do
      ctxptr <- primIO $ prim__next_cert_in_store cert_store prev_cert
      False <- nullPtr ctxptr
      | True => pure acc
      len <- primIO $ prim__cert_len_info ctxptr
      Just buffer <- newBuffer len
      | Nothing => loop acc cert_store ctxptr
      primIO $ prim__cert_body ctxptr buffer
      buffer_to_list buffer >>= \cert => loop (cert :: acc) cert_store ctxptr

--- END WINDOWS ---

--- START MACOS ---

rootCAKeyChain : String
rootCAKeyChain = "/System/Library/Keychains/SystemRootCertificates.keychain"

systemKeyChain : String
systemKeyChain = "/Library/Keychains/System.keychain"

command : List String
command = ["security", "find-certificate", "-pa", rootCAKeyChain, systemKeyChain]

read_pems : EitherT FileError IO String
read_pems = do
  file <- MkEitherT (popen command Read)
  MkEitherT (fRead file)

test_macos_cert : EitherT String IO ()
test_macos_cert = do
  pems <- bimapEitherT (\err => "popen security failed: \{show err}") id read_pems
  (pemblobs, _) <- MkEitherT $ pure $ parse (many parse_pem_blob) pems
  putStrLn "\{show (length pemblobs)} certificates found"
  let certs = map pem_to_certificate pemblobs
  traverse_ print_certificate certs

--- END MACOS ---

--- START UNIX ---

default_paths : List String
default_paths =
  [ "/etc/ssl/certs/"                 -- linux
  , "/system/etc/security/cacerts/"   -- android
  , "/usr/local/share/certs/"         -- freebsd
  , "/etc/ssl/cert.pem"               -- openbsd
  ]

to_files : HasIO io => List String -> io (List String)
to_files folders = join <$> traverse go folders where
  go : String -> io (List String)
  go folder = case !(listDir folder) of
    Left _ => pure [folder]
    Right files => pure (map (folder <+> "/" <+>) files)

test_unix_certs : EitherT String IO ()
test_unix_certs = do
  folder <- maybe default_paths (::[]) <$> getEnv "SYSTEM_CERTIFICATE_PATH"
  certpaths <- to_files folder
  pemtxts <- mapMaybe getRight <$> traverse readFile certpaths
  let pems = pemtxts >>= parse_pems_ignore_error
  let certs = map pem_to_certificate pems
  putStrLn "\{show (length certs)} certificates found"
  traverse_ {t=List} print_certificate certs
  where
    parse_pems_ignore_error : String -> List PEMBlob
    parse_pems_ignore_error = either (const []) fst . parse (many parse_pem_blob)

--- END UNIX

export
test_cert : EitherT String IO ()
test_cert =
  if isWindows
     then test_windows_cert
     else (if os == "darwin" then test_macos_cert else test_unix_certs)
