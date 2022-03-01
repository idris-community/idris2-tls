module LTLS

import Control.Monad.Error.Either
import Control.Linear.LIO
import Crypto.Random
import Crypto.Random.C
import Data.Either
import Data.List
import Data.List1
import Data.String
import Data.String.Extra
import Data.String.Parser
import Debug.Trace
import Network.Socket
import Network.TLS
import Network.TLS.Certificate.System
import System
import System.File.ReadWrite
import Utils.Bytes
import Utils.Handle
import Utils.Handle.C
import Utils.IPAddr
import Utils.Misc

||| Constructs a HTTP GET request given a hostname
test_http_body : String -> List Bits8
test_http_body hostname =
  string_to_ascii
  $ join "\r\n"
  [ "GET / HTTP/1.1"
  , "Host: " <+> hostname
  , "Connection: close"
  , "User-Agent: curl"
  , "Accept: */*"
  , "Content-Length: 0"
  , ""
  , ""
  ]

tls_connect : List Certificate -> String -> Int -> EitherT String IO (List Bits8)
tls_connect certs target_hostname port = do
  Right sock <- socket AF_INET Stream 0
  | Left err => throwE "unable to create socket: \{show err}"
  0 <- connect sock (Hostname target_hostname) port
  | _ => throwE "unable to connect"

  -- Here we begin TLS communication in a linear fasion
  MkEitherT $ run $ do
    let handle = socket_to_handle sock
    -- Perform handshake with the TLS server
    -- Here we supply the chosen cipher suites,
    -- key exhange groups for TLS handshake
    (True # handle) <-
      tls_handshake
        -- the hostname of the server to be connected to
        target_hostname
        -- the elliptic curves x25519, secp256r1, secp384r1
        -- are chosen for key exchange
        -- RFC 8446 specifies that secp256r1 MUST be supported,
        -- and x25519 SHOULD be supported as well
        -- We put x25519 first because we prefer x25519 over secp256r1
        -- since the x25519 implementation is faster and simpler
        -- secp384r1 is also added to test with https://ecc384.badssl.com/
        -- note that key generation can take some time, so I prefer to keep
        -- this list short
        -- more groups such as x448 and secp521r1 are implemented but not used
        -- here
        (X25519 ::: [SECP256r1, SECP384r1])
        -- here we specify the supported signature algorithms that will be
        -- used to verify TLS handshake given the server's certificate
        supported_signature_algorithms
        -- here we specify the supported cipher suites that will be used
        -- to encrypt communication with the server
        -- we want to support both TLS 1.3 and TLS 1.2 so we supply both
        (tls13_supported_cipher_suites <+> tls12_supported_cipher_suites)
        -- handle of the underlying socket
        handle
        -- the function which will be used to verify the server's certificate
        -- more documentation can be found in Network.TLS.Verify
        -- if you want to skip certificate verification, you can use certificate_ignore_check
        -- or implement your own CertificateCheck function
        -- (certificate_ignore_check target_hostname)
        (certificate_check certs target_hostname)
    | (False # (error # ())) => pure $ Left error

    -- send data to the server
    -- here I split the data to two chunks for testing purpose
    -- you can just send the data without splitting
    let (data1, data2) = splitAt 40 $ test_http_body target_hostname
    (True # handle) <- write handle data1
    | (False # (error # ())) => pure $ Left error

    (True # handle) <- write handle data2
    | (False # (error # ())) => pure $ Left error

    -- I did read twice here for testing purpose
    -- read 100 bytes of data from the server
    (True # (output1 # handle)) <- read handle 100
    | (False # (error # ())) => pure $ Left error

    -- read 100 bytes of data from the server again
    (True # (output2 # handle)) <- read handle 100
    | (False # (error # ())) => pure $ Left error

    close handle
    pure $ Right (output1 <+> output2)

||| Given a list of trusted certificates, server hostname, server port,
||| connect to the server and send a HTTP request.
||| Arguments:
|||
||| target_hostname : String
||| target_hostname is the hostname of the server to be connected. It can
||| be a DNS hostname, IPv4 address, or IPv6 address.
|||
||| port : Int
||| port is the port number of the server to be connected. The port number
||| for https server is 443.
tls_test : String -> Int -> IO ()
tls_test target_hostname port = do
  putStrLn "reading cert store"
  Right certs <- get_system_trusted_certs
  | Left err => putStrLn "error while reading: \{show err}"
  Right response <- runEitherT $ tls_connect certs target_hostname port
  | Left err => putStrLn err
  putStrLn (ascii_to_string response)
  putStrLn "ok"

tls_test_targets : List (Bool, String, Int)
tls_test_targets =
  [ (True, "sha256.badssl.com", 443)
  , (True, "sha384.badssl.com", 443)
  , (True, "sha512.badssl.com", 443)
  , (True, "github.com", 443)
  , (True, "google.com", 443)
  -- TODO: investigate why these 2 are not working
  -- , ("ecc256.badssl.com", 443)
  -- , ("ecc384.badssl.com", 443)
  , (True, "tls-v1-2.badssl.com", 1012)
  , (False, "expired.badssl.com", 443)
  , (False, "wrong.host.badssl.com", 443)
  , (False, "self.signed.badssl.com", 443)
  , (False, "untrusted-root.badssl.com", 443)
  ]

export
tls_test_unit : EitherT String IO ()
tls_test_unit = do
  putStrLn "reading cert store"
  certs <- MkEitherT get_system_trusted_certs
  results <- liftIO $ traverse (go certs) tls_test_targets
  let [] = filter not results
  | failed => throwE "\{show $ length failed} tls connections failed"
  pure ()
  where
    go : List Certificate -> (Bool, String, Int) -> IO Bool
    go certs (should_work, target, port) = do
      putStr "testing on \{target} \{show port}: "
      Right _ <- runEitherT $ tls_connect certs target port
      | Left err =>
          if should_work
             then putStrLn "error: \{err}" $> False
             else putStrLn "expected error: \{err}" $> True
      if should_work
         then putStrLn "ok" $> True
         else putStrLn "ok when it should not be ok" $> False
