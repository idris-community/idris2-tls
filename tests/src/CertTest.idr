module CertTest

import Data.Vect
import Data.Fin
import Control.Monad.Error.Either
import System.Info
import System.FFI
import Data.Buffer
import Network.TLS.Certificate

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

print_certificate : HasIO io => Either String Certificate -> io ()
print_certificate (Right cert) = printLn cert
print_certificate (Left err) = putStrLn "cannot parse: \{err}"

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

export
test_cert : EitherT String IO ()
test_cert =
  if isWindows
     then test_windows_cert
     else putStrLn "not on windows, skipped"
