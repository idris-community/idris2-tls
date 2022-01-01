module Tests.LTLS

import Network.TLS
import Network.TLS.Handshake
import Network.TLS.Handle
import Network.TLS.Certificate
import Network.Socket
import Crypto.Random.C
import Crypto.Random
import Utils.Handle.C
import Utils.Handle
import Control.Linear.LIO
import Utils.Misc
import Utils.Bytes
import Data.String
import Data.List1
import Utils.IPAddr
import Data.Either

import Debug.Trace

domain_predicate : String -> Maybe (String -> Bool)
domain_predicate predicate = do
  let parts = split ('.' ==) predicate
  guard $ verify_predicate parts
  Just (apply_predicate parts . split ('.' == ))
  where
    str_eq : String -> String -> Lazy Bool
    str_eq "*" _ = delay True
    str_eq _ "*" = delay True
    str_eq a b = delay (a == b)
    apply_predicate : List1 String -> List1 String -> Bool
    apply_predicate a b = (length a == length b) && (and $ zipWith str_eq a b)
    verify_predicate : List1 String -> Bool
    verify_predicate ("*" ::: []) = False
    verify_predicate ("*" ::: [_]) = False
    verify_predicate ("*" ::: [_, ""]) = False
    verify_predicate ("*" ::: xs) = and $ map (delay . not . isInfixOf "*") xs
    verify_predicate xs = and $ map (delay . not . isInfixOf "*") (toList xs)

domain_predicate' : String -> (String -> Bool)
domain_predicate' predicate =
  case domain_predicate predicate of
    Nothing => const False
    Just f => f

test_http_body : String -> List Bits8
test_http_body hostname = string_to_ascii $ "GET / HTTP/1.1\nHost: " <+> hostname <+> "\n\n"

check_ipv4_address : List GeneralName -> IPv4Addr -> Bool
check_ipv4_address (IPv4Addr addr' :: xs) addr = if addr == addr' then True else check_ipv4_address xs addr
check_ipv4_address (x :: xs) addr = check_ipv4_address xs addr
check_ipv4_address [] _ = False

check_ipv6_address : List GeneralName -> IPv6Addr -> Bool
check_ipv6_address (IPv6Addr addr' :: xs) addr = if addr == addr' then True else check_ipv6_address xs addr
check_ipv6_address (x :: xs) addr = check_ipv6_address xs addr
check_ipv6_address [] _ = False

check_dns_name : List GeneralName -> String -> Bool
check_dns_name (DNSName predicate :: xs) name = if (domain_predicate' predicate) name then True else check_dns_name xs name
check_dns_name (x :: xs) name = check_dns_name xs name
check_dns_name [] _ = False

Identifier : Type
Identifier = Eithers [IPv4Addr, IPv6Addr, String]

find_certificate : Identifier -> List (Network.TLS.Certificate.Certificate) -> Maybe (Network.TLS.Certificate.Certificate)
find_certificate identifier certs = choice $ map (delay . is_certificate identifier) certs
  where
    is_certificate : Identifier -> Network.TLS.Certificate.Certificate -> Maybe (Network.TLS.Certificate.Certificate)
    is_certificate (Left x)          cert = guard (check_ipv4_address (certificate_subject_names cert) x) $> cert
    is_certificate (Right (Left x))  cert = guard (check_ipv6_address (certificate_subject_names cert) x) $> cert
    is_certificate (Right (Right x)) cert = guard (check_dns_name (certificate_subject_names cert) x) $> cert

to_identifier : String -> Identifier
to_identifier hostname =
  case parse_ipv4 hostname of
    Right x => Left x
    Left _ =>
      case parse_ipv6 hostname of
        Right x => Right (Left x)
        Left _ => Right (Right hostname)

-- TODO: implement this
certificate_check : String -> CertificateCheck IO
certificate_check hostname cert = do
  let certificates = body <$> cert.certificates
  case the _ $ traverse parse_certificate certificates of
    Right ok => do
      let identifer = to_identifier hostname
      let Just cert = find_certificate identifer ok
      | Nothing => putStrLn "cannot find certificate" $> False
      putStrLn $ show cert
      pure True
    Left err => putStrLn err $> False

tls_test : String -> Int -> IO ()
tls_test target_hostname port = do
  Right sock <- socket AF_INET Stream 0
  | Left err => putStrLn $ "unable to create socket: " <+> show err
  0 <- connect sock (Hostname target_hostname) port
  | _ => putStrLn "unable to connect"
  run $ do
    let handle = socket_to_handle sock
    -- perform handshake
    (True # handle) <- tls_handshake target_hostname handle (certificate_check target_hostname)
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
