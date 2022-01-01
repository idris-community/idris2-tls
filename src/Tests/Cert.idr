module Tests.Cert

import Data.List
import Utils.Misc
import Utils.Bytes
import Utils.Parser
import Network.TLS.Parse.PEM
import Network.TLS.Parse.DER
import Network.TLS.Parsing
import Data.String.Parser
import Network.TLS.Signature
import Network.TLS.Certificate

import System.File.ReadWrite

import Debug.Trace

parse_report_error : List Certificate -> List PEMBlob -> Either String (List Certificate)
parse_report_error acc [] = Right acc
parse_report_error acc (x :: xs) =
  case parse_certificate x.content of
    Right cert => parse_report_error (cert :: acc) xs
    Left err => Left $ "error: " <+> err <+> ", content:\n" <+> encode_pem_blob x

-- Download it from https://wiki.mozilla.org/CA/Included_Certificates
test_cert_list : HasIO io => String -> io ()
test_cert_list cert_store_path = do
  Right certs_txt <- readFile cert_store_path
  | Left err => putStrLn $ "error while reading: " <+> show err

  let Right (certs_bin, _) = parse (many parse_pem_blob) certs_txt
  | Left err => putStrLn $ "error while parsing pem: " <+> err

  let Right certs = parse_report_error [] certs_bin
  | Left err => putStrLn $ "error while parsing crt: " <+> err

  putStrLn $ show $ length certs
  putStrLn "ok"
