module Tests.Parse

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

import Debug.Trace

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

test_publickey : String
test_publickey =
  """
  -----BEGIN PUBLIC KEY-----
  MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAxIA2BrrnR2sIlATsp7aR
  BD/3krwZ7vt9dNeoDQAee0s6SuYP6MBx/HPnAkwNvPS90R05a7pwRkoT6Ur4PfPh
  CVlUe8lV+0Eto3ZSEeHz3HdsqlM3bso67L7Dqrc7MdVstlKcgJi8yeAoGOIL9/ig
  Ov0XBFCeznm9nznx6mnsR5cugw+1ypXelaHmBCLV7r5SeVSh57+KhvZGbQ2fFpUa
  TPegRpJZXBNS8lSeWvtOv9d6N5UBROTAJodMZT5AfX0jB0QB9IT/0I96H6BSENH0
  8NXOeXApMuLKvnAf361rS7cRAfRLrWZqERMP4u6Cnk0Cnckc3WcW27kGGIbtwbqU
  IQIDAQAB
  -----END PUBLIC KEY-----
  """

test_ecdsa : String
test_ecdsa =
  """
  -----BEGIN PUBLIC KEY-----
  MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAErfb3dbHTSVQKXRBxvdwlBksiHKIj
  Tp+h/rnQjL05vAwjx8+RppBa2EWrAxO+wSN6ucTInUf2luC5dmtQNmb3DQ==
  -----END PUBLIC KEY-----
  """


partial
test_der : HasIO io => io ()
test_der = do
  let Right (blob, _) = parse parse_pem_blob test_certificate
  | Left err => putStrLn err
  putStrLn "certificate"

  {-
  let Right (pk, _) = parse parse_pem_blob test_ecdsa
  | Left err => putStrLn err
  putStrLn "publickey"

 
  let Right pk = extract_key pk.content
  | Left err => putStrLn err
  -}

  let Right certificate = parse_certificate blob.content
  
  putStrLn "ok"
