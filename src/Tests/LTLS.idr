module Tests.LTLS

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
  | Left err => putStrLn $ "error while reading: " <+> show err

  -- Print the number of trusted certificates
  putStrLn $ "done, found " <+> show (length certs)

  Right sock <- socket AF_INET Stream 0
  | Left err => putStrLn $ "unable to create socket: " <+> show err
  0 <- connect sock (Hostname target_hostname) port
  | _ => putStrLn "unable to connect"

  -- Here we begin TLS communication in a linear fasion
  run $ do
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
    | (False # (error # ())) => putStrLn error

    putStrLn "sending data over tls"
    -- send data to the server
    -- here I split the data to two chunks for testing purpose
    -- you can just send the data without splitting
    let (data1, data2) = splitAt 40 $ test_http_body target_hostname
    (True # handle) <- write handle data1
    | (False # (error # ())) => putStrLn error

    (True # handle) <- write handle data2
    | (False # (error # ())) => putStrLn error

    putStrLn "reading data over tls"
    -- I did read twice here for testing purpose
    -- read 100 bytes of data from the server
    (True # (output # handle)) <- read handle 100
    | (False # (error # ())) => putStrLn error

    putStrLn "response"
    putStrLn $ ascii_to_string output

    -- read 100 bytes of data from the server again
    (True # (output # handle)) <- read handle 100
    | (False # (error # ())) => putStrLn error

    putStrLn "response"
    putStrLn $ ascii_to_string output

    -- close handle
    close handle
    putStrLn "ok"
