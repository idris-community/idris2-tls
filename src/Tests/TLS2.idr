module Tests.TLS2

import Crypto.AEAD
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
import Utils.Network
import Utils.Parser

-- TODO: FIX: takes about 1 second to compile for some reason
smart_read' : (Cons (Posed Bits8) i, Monoid i, HasIO m) => Socket -> Nat -> Parser i (SimpleError String) a -> m (List Bits8, (Either String a))
smart_read' sock pos (Pure leftover x) = do
  pure ([], Right x)
smart_read' sock pos (Fail err) = do
  pure ([], Left $ "parser stopped at position " <+> show pos <+> ": " <+> show err)
smart_read' sock pos parser = do
  Just bs <- recv_bytes sock 1
  | Nothing => pure ([], Left "recv_bytes failed")
  case bs of
    (b :: []) => map (mapFst (b ::)) $ smart_read' sock (S pos) (feed (singleton $ MkPosed pos b) parser)
    _ => pure $ (bs, Left $ "weird list returned from recv_byte: " <+> xxd bs)

-- inefficient but it is more pleasant to work with, can get stuck potentially
smart_read : (Cons (Posed Bits8) i, Monoid i, HasIO m) => Socket -> Parser i (SimpleError String) a -> m (List Bits8, Either String a)
smart_read sock parser = smart_read' sock 0 parser

test_http_body : String -> String
test_http_body hostname = "GET / HTTP/1.1\nHost: " <+> hostname <+> "\n\n"

example_hostname : String
example_hostname = "hkust.edu.hk"

-- TODO: FIX: takes about ~30 seconds to compile for some reason
partial
tls_test : HasIO m => (target_hostname : String) -> m ()
tls_test target_hostname = do
  Right sock <- socket AF_INET Stream 0
  | Left err => putStrLn $ "unable to create socket: " <+> show err

  putStrLn $ "generate key pair"
  -- (sk, pk) <- generate_key_pair {a=X25519_DH}
  let sk = the (Vect 32 Bits8) $
    [ 0xcc, 0x93, 0x5d, 0xb7, 0x60, 0x54, 0xe7, 0x2d, 0x3a, 0x29, 0xcb, 0x62, 0x5d, 0xc0, 0x10, 0xca, 0x6d
    , 0x46, 0x0e, 0xf6, 0x56, 0xf5, 0x06, 0xa5, 0xbb, 0x50, 0x4a, 0xb0, 0x68, 0x28, 0x34, 0x30]
  let pk = the (Vect 32 Bits8) $
    [ 0x38, 0xf3, 0xa1, 0xf3, 0xa8, 0x3b, 0x6c, 0x55, 0x88, 0x9a, 0x4b, 0x5d, 0x62, 0x81, 0x70, 0xf5, 0xe6
    , 0xca, 0x09, 0x60, 0xb9, 0x3b, 0x4a, 0xd8, 0x95, 0x59, 0x00, 0x2d, 0x72, 0x78, 0x9d, 0x24 ]

  putStrLn $ ("private key: " <+> (xxd $ toList sk))
  putStrLn $ ("public key: " <+> (xxd $ toList pk))

  putStrLn $ "connecting to " <+> target_hostname
  0 <- connect sock (Hostname target_hostname) 443
  | _ => putStrLn $ "unable to connect"
  putStrLn $ "connected"

  putStrLn $ "generating random"
  let random = map (cast . finToNat) range
  putStrLn $ "random: " <+> xxd (toList random)
  session <- random_bytes 0
  putStrLn $ "session: " <+> xxd (toList session)

  let
    client_hello_object =
      MkClientHello
        TLS12
        random
        (toList session)
        ( TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 :::
        [ TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
        , TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
        , TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ])
        (singleton Null)
        [ (_ ** ServerName $ DNS target_hostname ::: [])
        , (_ ** SupportedGroups $ X25519 ::: [SECP256r1])
        , (_ ** SignatureAlgorithms $ RSA_PKCS1_SHA256 ::: [RSA_PSS_RSAE_SHA256, ECDSA_SECP256r1_SHA256])
        , (_ ** KeyShare $ singleton (X25519, serialize_pk {a=X25519_DH} pk))
        , (_ ** SupportedVersions $ TLS13 ::: [])
        ]

  putStrLn $ "sending client hello"
  let b_client_hello = (arecord2 {i = List (Posed Bits8)}).encode (TLS12, (_ ** Handshake [(_ ** ClientHello client_hello_object)]))
  putStrLn $ "client hello: " <+> xxd b_client_hello
  _ <- send_bytes sock b_client_hello

  putStrLn $ "reading server hello"
  (b_server_response, (Right (Right (TLS12, MkDPair _ (Handshake [MkDPair _ (ServerHello server_hello)])))))
    <- smart_read {i = List (Posed Bits8)} sock alert_or_arecord2.decode
  | (b_server_response, server_response) => (putStrLn $ show $ length b_server_response) *> (putStrLn $ "unexpected server response: " <+> show server_response)
  putStrLn $ "server hello: " <+> show server_hello

  let TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 = cipher_suite server_hello
  | other => putStrLn $ "unexpected cipher suite: " <+> (show other)

  let TLS12 = get_server_version server_hello
  | other => putStrLn $ "unexpected TLS version: " <+> (show other)

  (b_server_response, (Right (Right (TLS12, MkDPair _ (Handshake [MkDPair _ (Certificate server_certificate)])))))
    <- smart_read {i = List (Posed Bits8)} sock alert_or_arecord2.decode
  | (sus, other) => (putStrLn (xxd sus)) *> (putStrLn (show $ length sus)) *> print other

  putStrLn "server certificate received"
  putStrLn $ show server_certificate

  putStrLn "TODO"
