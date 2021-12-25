module Tests.Parse

import Data.List
import Utils.Misc
import Utils.Bytes
import Utils.Parser
import Network.TLS.Parse.PEM
import Network.TLS.Parse.DER
import Network.TLS.Parsing
import Data.String.Parser

test_certificate : String
test_certificate =
  """
  The test certificate
  Useless comments
  -----BEGIN CERTIFICATE-----
  MIIDfDCCAmSgAwIBAgIJAJB2iRjpM5OgMA0GCSqGSIb3DQEBCwUAME4xMTAvBgNV
  BAsMKE5vIFNOSSBwcm92aWRlZDsgcGxlYXNlIGZpeCB5b3VyIGNsaWVudC4xGTAX
  BgNVBAMTEGludmFsaWQyLmludmFsaWQwHhcNMTUwMTAxMDAwMDAwWhcNMzAwMTAx
  MDAwMDAwWjBOMTEwLwYDVQQLDChObyBTTkkgcHJvdmlkZWQ7IHBsZWFzZSBmaXgg
  eW91ciBjbGllbnQuMRkwFwYDVQQDExBpbnZhbGlkMi5pbnZhbGlkMIIBIjANBgkq
  hkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAzWJP5cMThJgMBeTvRKKl7N6ZcZAbKDVA
  tNBNnRhIgSitXxCzKtt9rp2RHkLn76oZjdNO25EPp+QgMiWU/rkkB00Y18Oahw5f
  i8s+K9dRv6i+gSOiv2jlIeW/S0hOswUUDH0JXFkEPKILzpl5ML7wdp5kt93vHxa7
  HswOtAxEz2WtxMdezm/3CgO3sls20wl3W03iI+kCt7HyvhGy2aRPLhJfeABpQr0U
  ku3q6mtomy2cgFawekN/X/aH8KknX799MPcuWutM2q88mtUEBsuZmy2nsjK9J7/y
  hhCRDzOV/yY8c5+l/u/rWuwwkZ2lgzGp4xBBfhXdr6+m9kmwWCUm9QIDAQABo10w
  WzAOBgNVHQ8BAf8EBAMCAqQwHQYDVR0lBBYwFAYIKwYBBQUHAwEGCCsGAQUFBwMC
  MA8GA1UdEwEB/wQFMAMBAf8wGQYDVR0OBBIEELsPOJZvPr5PK0bQQWrUrLUwDQYJ
  KoZIhvcNAQELBQADggEBALnZ4lRc9WHtafO4Y+0DWp4qgSdaGygzS/wtcRP+S2V+
  HFOCeYDmeZ9qs0WpNlrtyeBKzBH8hOt9y8aUbZBw2M1F2Mi23Q+dhAEUfQCOKbIT
  tunBuVfDTTbAHUuNl/eyr78v8Egi133z7zVgydVG1KA0AOSCB+B65glbpx+xMCpg
  ZLux9THydwg3tPo/LfYbRCof+Mb8I3ZCY9O6FfZGjuxJn+0ux3SDora3NX/FmJ+i
  kTCTsMtIFWhH3hoyYAamOOuITpPZHD7yP0lfbuncGDEqAQu2YWbYxRixfq2VSxgv
  gWbFcmkgBLYpE8iDWT3Kdluo1+6PHaDaLg2SacOY6Go=
  -----END CERTIFICATE-----
  """

test_certificate2 : String
test_certificate2 =
  """
  -----BEGIN CERTIFICATE-----
  MIIFKDCCBM+gAwIBAgIQAdIfyDzGygOhDxOVwqcmHDAKBggqhkjOPQQDAjBKMQsw
  CQYDVQQGEwJVUzEZMBcGA1UEChMQQ2xvdWRmbGFyZSwgSW5jLjEgMB4GA1UEAxMX
  Q2xvdWRmbGFyZSBJbmMgRUNDIENBLTMwHhcNMjEwOTE4MDAwMDAwWhcNMjIwOTE3
  MjM1OTU5WjByMQswCQYDVQQGEwJVUzETMBEGA1UECBMKQ2FsaWZvcm5pYTEWMBQG
  A1UEBxMNU2FuIEZyYW5jaXNjbzEZMBcGA1UEChMQQ2xvdWRmbGFyZSwgSW5jLjEb
  MBkGA1UEAxMSd3d3LmNsb3VkZmxhcmUuY29tMFkwEwYHKoZIzj0CAQYIKoZIzj0D
  AQcDQgAE4oAICmiZSBhltLFYAuI14RPj9CXN1D0bCFvGl8fJ74BDOoKKE7MPn6uK
  Y88Jwmc4a5nGWnykGd6eL0E1NSOFHqOCA20wggNpMB8GA1UdIwQYMBaAFKXON+rr
  sHUOlGeItEX62SQQh5YfMB0GA1UdDgQWBBSATUpCMq4Jj1EHS6jU1Haou0GwMTAz
  BgNVHREELDAqghQqLnd3dy5jbG91ZGZsYXJlLmNvbYISd3d3LmNsb3VkZmxhcmUu
  Y29tMA4GA1UdDwEB/wQEAwIHgDAdBgNVHSUEFjAUBggrBgEFBQcDAQYIKwYBBQUH
  AwIwewYDVR0fBHQwcjA3oDWgM4YxaHR0cDovL2NybDMuZGlnaWNlcnQuY29tL0Ns
  b3VkZmxhcmVJbmNFQ0NDQS0zLmNybDA3oDWgM4YxaHR0cDovL2NybDQuZGlnaWNl
  cnQuY29tL0Nsb3VkZmxhcmVJbmNFQ0NDQS0zLmNybDA+BgNVHSAENzA1MDMGBmeB
  DAECAjApMCcGCCsGAQUFBwIBFhtodHRwOi8vd3d3LmRpZ2ljZXJ0LmNvbS9DUFMw
  dgYIKwYBBQUHAQEEajBoMCQGCCsGAQUFBzABhhhodHRwOi8vb2NzcC5kaWdpY2Vy
  dC5jb20wQAYIKwYBBQUHMAKGNGh0dHA6Ly9jYWNlcnRzLmRpZ2ljZXJ0LmNvbS9D
  bG91ZGZsYXJlSW5jRUNDQ0EtMy5jcnQwDAYDVR0TAQH/BAIwADCCAX4GCisGAQQB
  1nkCBAIEggFuBIIBagFoAHYAKXm+8J45OSHwVnOfY6V35b5XfZxgCvj5TV0mXCVd
  x4QAAAF79j4m0AAABAMARzBFAiEAvKDJ5n/u7CgYVtco9JCPRbZJq/z82l9HFlZA
  u+xCmkcCIDI25qHABDHpxIf6Y6Vyzfbx6YqtXbH9qaDcGWrU7Gq+AHYAUaOw9f0B
  eZxWbbg3eI8MpHrMGyfL956IQpoN/tSLBeUAAAF79j4nPgAABAMARzBFAiBTDKQr
  x0RKDWbCh9TzLUERGevPkPYMna4J6Tx9ar1dIQIhALQ0UM+WOHzDM59V454jiTKE
  yEiML9y/X9BMkI/+YdlrAHYAQcjKsd8iRkoQxqE6CUKHXk4xixsD6+tLx2jwkGKW
  BvYAAAF79j4nEgAABAMARzBFAiEA7SA5gPLY4H484JBw4CKagi6S/c3aZJV/tBWj
  yuNBS3cCIG8tZ6o7tbPO6xnlH4uqOFv8SmpLLe1UQNDKPxzsw6BSMAoGCCqGSM49
  BAMCA0cAMEQCIGhqV3zVr73qOPWtWrAM9Rws7JtjI63UlTJHofnjxiabAiAiMGF7
  IF0SAGLGP8LXoFc913Pe30/OqeK0MI+LgAhcPw==
  -----END CERTIFICATE-----
  """

partial
test_der : HasIO io => io ()
test_der = do
  let Right (blob, _) = parse parse_pem_blob test_certificate2
  | Left err => putStrLn err
  putStrLn "certificate"
  -- putStrLn $ xxd blob.content

  let (Pure [] ok) = feed (map (uncurry MkPosed) $ enumerate Z blob.content) parse_asn1
  | (Pure leftover _) => putStrLn $ "leftover: " <+> (xxd $ map get leftover)
  | (Fail err) => putStrLn $ show err

  let (Universal ** 16 ** Sequence
        [ (Universal ** 16 ** Sequence
          ( (ContextSpecific ** 0 ** UnknownConstructed _ _ [ (Universal ** 2 ** IntVal version) ])
          :: (Universal ** 2 ** IntVal serial_number)
          :: (Universal ** 16 ** Sequence ((Universal ** 6 ** crt_signature_algorithm) :: crt_signature_parameter))
          :: (Universal ** 16 ** Sequence issuer)
          :: (Universal ** 16 ** Sequence
              [ valid_not_before
              , valid_not_after
              ])
          :: (Universal ** 16 ** Sequence subject)
          :: (Universal ** 16 ** Sequence
              [ (Universal ** 16 ** Sequence ((Universal ** 6 ** tbs_signature_algorithm) :: tbs_signature_parameter))
              , (Universal ** 3 ** Bitstring tbs_subject_public_key)
              ])
          :: optional_fields
          ))
        , (Universal ** 16 ** Sequence ((Universal ** 6 ** signature_algorithm) :: signature_parameter))
        , (Universal ** 3 ** Bitstring signature_value)
        ]
      ) = ok

  putStrLn $ show serial_number
  putStrLn "ok"
