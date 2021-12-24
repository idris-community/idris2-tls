module Tests.LTLS

import Network.TLS
import Network.TLS.Handshake
import Network.TLS.Handle
import Network.Socket
import Crypto.Random.C
import Crypto.Random
import Utils.Handle.C
import Utils.Handle
import Control.Linear.LIO
import Utils.Misc
import Utils.Bytes

test_http_body : String -> List Bits8
test_http_body hostname = string_to_ascii $ "GET / HTTP/1.1\nHost: " <+> hostname <+> "\n\n"

-- TODO: implement this
certificate_check : CertificateCheck IO
certificate_check = const $ pure True 

tls_test : String -> Int -> IO ()
tls_test target_hostname port = do
  Right sock <- socket AF_INET Stream 0
  | Left err => putStrLn $ "unable to create socket: " <+> show err
  0 <- connect sock (Hostname target_hostname) port
  | _ => putStrLn "unable to connect"
  run $ do
    let handle = socket_to_handle sock
    -- perform handshake
    (True # handle) <- tls_handshake target_hostname handle certificate_check
    | (False # (error # ())) => putStrLn error

    -- write data
    (True # handle) <- write handle $ test_http_body target_hostname
    | (False # (error # ())) => putStrLn error

    -- read data
    (True # (output # handle)) <- read handle 100
    | (False # (error # ())) => putStrLn error

    putStrLn "response"
    putStrLn $ ascii_to_string output

    -- read data
    (True # (output # handle)) <- read handle 100
    | (False # (error # ())) => putStrLn error

    putStrLn "response"
    putStrLn $ ascii_to_string output

    -- close handle
    close handle
    putStrLn "ok"

