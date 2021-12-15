module Network.TLS.Handshake

import Data.List1
import Data.Vect
import Network.TLS.HelloExtension
import Network.TLS.Magic
import Network.TLS.Parsing
import Utils.Bytes
import Utils.Misc
import Utils.Show

||| the only extensions that can found in wrappers during handshake
public export
data WhenWrapped : HandshakeType -> Type where
  IsEncryptedExtensions : WhenWrapped EncryptedExtensions
  IsCertificate : WhenWrapped Certificate
  IsCertificateVerify : WhenWrapped CertificateVerify
  IsFinished : WhenWrapped Finished
  IsNewSessionTicket : WhenWrapped NewSessionTicket

public export
Uninhabited (WhenWrapped ClientHello) where
  uninhabited _ impossible

public export
Uninhabited (WhenWrapped ServerHello) where
  uninhabited _ impossible

public export
dec_when_wrapped : (type : HandshakeType) -> Dec (WhenWrapped type)
dec_when_wrapped EncryptedExtensions = Yes IsEncryptedExtensions
dec_when_wrapped Certificate = Yes IsCertificate
dec_when_wrapped CertificateVerify = Yes IsCertificateVerify
dec_when_wrapped Finished = Yes IsFinished
dec_when_wrapped NewSessionTicket = Yes IsNewSessionTicket
dec_when_wrapped ClientHello = No uninhabited
dec_when_wrapped ServerHello = No uninhabited

namespace Message
  public export
  record ClientHello where
    constructor MkClientHello
    version : TLSVersion
    random : Vect 32 Bits8
    session_id : List Bits8
    cipher_suites : List1 CipherSuite
    compression_levels : List1 CompressionLevel
    extensions : List (DPair _ ClientExtension)

  public export
  Show ClientHello where
    show x = show_record "ClientHello"
      [ ("version", show x.version)
      , ("random", xxd $ toList x.random)
      , ("session_id", xxd x.session_id)
      , ("cipher_suites", show x.cipher_suites)
      , ("compression_levels", show x.compression_levels)
      , ("extensions", show $ map (\x => show x.snd) x.extensions)
      ]

  public export
  record ServerHello where
    constructor MkServerHello
    version : TLSVersion
    random : Vect 32 Bits8
    session_id : List Bits8
    cipher_suite : CipherSuite
    compression_level : CompressionLevel
    extensions : List (DPair _ ServerExtension)

  public export
  Show ServerHello where
    show x = show_record "ClientHello"
      [ ("version", show x.version)
      , ("random", xxd $ toList x.random)
      , ("session_id", xxd x.session_id)
      , ("cipher_suite", show x.cipher_suite)
      , ("compression_level", show x.compression_level)
      , ("extensions", show $ map (\x => show x.snd) x.extensions)
      ]

  public export
  record EncryptedExtensions where
    constructor MkEncryptedExtensions
    get : List Bits8 -- TODO: how would it work?

  public export
  Show EncryptedExtensions where
    show x = show_record "EncryptedExtensions"
      [ ("get", xxd x.get)
      ]

  public export
  record Certificate where
    constructor MkCertificate
    request_context : List Bits8
    certificates : List1 (List Bits8)
    certificate_extensions : List Bits8 -- TODO: how would it work?

  public export
  Show Certificate where
    show x = show_record "Certificate"
      [ ("request_context", xxd x.request_context)
      , ("certificates", show $ map xxd $ x.certificates)
      , ("certificate_extensions", xxd x.certificate_extensions)
      ]

  public export
  record CertificateVerify where
    constructor MkCertificateVerify
    signature_algorithm : SignatureAlgorithm
    signature : List Bits8

  public export
  Show CertificateVerify where
    show x = show_record "CertificateVerify"
      [ ("signature_algorithm", show x.signature_algorithm)
      , ("signature", xxd x.signature)
      ]

  public export
  record Finished where
    constructor MkFinished
    verify_data : List Bits8

  public export
  Show Finished where
    show x = show_record "Finished"
      [ ("verify_data", show x.verify_data)
      ]

  public export
  record NewSessionTicket where
    constructor MkNewSessionTicket
    lifetime_seconds : Nat
    age_add_milliseconds : Nat
    nonce : List Bits8
    session_ticket : List Bits8
    extensions : List ((Bits8, Bits8), List Bits8)

  public export
  Show NewSessionTicket where
    show x = show_record "NewSesssionTicket"
      [ ("lifetime_seconds", show x.lifetime_seconds)
      , ("age_add_milliseconds", show x.age_add_milliseconds)
      , ("nonce", show x.nonce)
      , ("session_ticket", show x.session_ticket)
      , ("extensions", show x.extensions)
      ]

public export
data Handshake : HandshakeType -> Type where
  ClientHello : ClientHello -> Handshake ClientHello
  ServerHello : ServerHello -> Handshake ServerHello
  EncryptedExtensions : EncryptedExtensions -> Handshake EncryptedExtensions
  Certificate : Certificate -> Handshake Certificate
  CertificateVerify : CertificateVerify -> Handshake CertificateVerify
  Finished : Finished -> Handshake Finished
  NewSessionTicket : NewSessionTicket -> Handshake NewSessionTicket

public export
Show (Handshake type) where
  show (ClientHello x) = show x
  show (ServerHello x) = show x
  show (EncryptedExtensions x) = show x
  show (Certificate x) = show x
  show (CertificateVerify x) = show x
  show (Finished x) = show x
  show (NewSessionTicket x) = show x

XHandshake : Type
XHandshake = Eithers [Handshake ClientHello, Handshake ServerHello, Handshake EncryptedExtensions, Handshake Certificate, Handshake CertificateVerify, Handshake Finished, Handshake NewSessionTicket]

hack_handshake : DPair _ Handshake -> XHandshake
hack_handshake (ClientHello ** x)         = Left x
hack_handshake (ServerHello ** x)         = Right (Left x)
hack_handshake (EncryptedExtensions ** x) = Right (Right (Left x))
hack_handshake (Certificate ** x)         = Right (Right (Right (Left x)))
hack_handshake (CertificateVerify ** x)   = Right (Right (Right (Right (Left x))))
hack_handshake (Finished ** x)            = Right (Right (Right (Right (Right (Left x)))))
hack_handshake (NewSessionTicket ** x)    = Right (Right (Right (Right (Right (Right x)))))

fix_handshake : XHandshake -> DPair _ Handshake
fix_handshake (Left x)                                          = (ClientHello ** x)
fix_handshake (Right (Left x))                                  = (ServerHello ** x)
fix_handshake (Right (Right (Left x)))                          = (EncryptedExtensions ** x)
fix_handshake (Right (Right (Right (Left x))))                  = (Certificate ** x)
fix_handshake (Right (Right (Right (Right (Left x)))))          = (CertificateVerify ** x)
fix_handshake (Right (Right (Right (Right (Right (Left x))))))  = (Finished ** x)
fix_handshake (Right (Right (Right (Right (Right (Right x)))))) = (NewSessionTicket ** x)

namespace Parsing
  export
  handshake_id_with_length : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (HandshakeType, Nat)
  handshake_id_with_length = handshake_type <*>> nat 3

  export
  no_id_client_hello : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake ClientHello)
  no_id_client_hello = map (\(a,b,c,d,e,f) => ClientHello (MkClientHello a b c d e f)) (\(ClientHello (MkClientHello a b c d e f)) => (a,b,c,d,e,f))
    $ lengthed 3
    $ under "client version" tls_version
    <*>> (under "client random" $ ntokens 32)
    <*>> (under "session id" $ lengthed_list 1 token)
    <*>> (under "client proposed cipher suites" $ lengthed_list1 2 cipher_suite)
    <*>> (under "client proposed compression levels" $ lengthed_list1 1 compression_level)
    <*>> (under "client extensions" $ lengthed_list 2 extension)

  export
  no_id_server_hello : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake ServerHello)
  no_id_server_hello = map (\(a,b,c,d,e,f) => ServerHello (MkServerHello a b c d e f)) (\(ServerHello (MkServerHello a b c d e f)) => (a,b,c,d,e,f))
    $ lengthed 3
    $ (under "server version" tls_version)
    <*>> (under "server random" $ ntokens 32)
    <*>> (under "session id" $ lengthed_list 1 token)
    <*>> (under "server chosen cipher suite" $ cipher_suite)
    <*>> (under "server chosen compression level" $ compression_level)
    <*>> (under "server extensions" $ lengthed_list 2 extension)

  export
  no_id_encrypted_extensions : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake EncryptedExtensions)
  no_id_encrypted_extensions = map (\a => EncryptedExtensions (MkEncryptedExtensions a)) (\(EncryptedExtensions (MkEncryptedExtensions a)) => a)
    $ lengthed 3
    $ (under "encrypted extensions body" $ lengthed_list 2 token)

  export
  no_id_certificate : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake Certificate)
  no_id_certificate = map (\(a,b,c) => Certificate (MkCertificate a b c)) (\(Certificate (MkCertificate a b c)) => (a,b,c))
    $ lengthed 3
    $ (under "request context" $ lengthed_list 1 token)
    <*>> (under "certificates" $ lengthed 3 $ under "certificate list" $ lengthed_list1 3 $ under "certificate entry" $ lengthed_list 3 token)
    <*>> (under "certificate extensions" $ lengthed_list 2 token)

  export
  no_id_certificate2 : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake Certificate)
  no_id_certificate2 = map (\(b) => Certificate (MkCertificate [] b [])) (\(Certificate (MkCertificate a b c)) => b)
    $ lengthed 3
    $ (under "certificate list 1.2" $ lengthed_list1 3 $ under "certificate entry 1.2" $ lengthed_list 3 token)

  export
  no_id_certificate_verify : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake CertificateVerify)
  no_id_certificate_verify = map (\(a,b) => CertificateVerify (MkCertificateVerify a b)) (\(CertificateVerify (MkCertificateVerify a b)) => (a,b))
    $ lengthed 3
    $ signature_algorithm
    <*>> (under "signature" $ lengthed_list 2 token)

  export
  no_id_finished : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake Finished)
  no_id_finished = map (\a => Finished (MkFinished a)) (\(Finished (MkFinished a)) => a)
    $ lengthed_list 3 token

  export
  no_id_new_session_ticket : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake NewSessionTicket)
  no_id_new_session_ticket = map (\(a,b,c,d,e) => NewSessionTicket (MkNewSessionTicket a b c d e)) (\(NewSessionTicket (MkNewSessionTicket a b c d e)) => (a,b,c,d,e))
    $ lengthed 3
    $ (under "ticket lifetime seconds" $ nat 4)
    <*>> (under "ticket age add milliseconds" $ nat 4)
    <*>> (under "ticket nonce" $ lengthed_list 1 token)
    <*>> (under "session ticket" $ lengthed_list 2 token)
    <*>> (under "extensions" $ lengthed_list 2 ((token <*>> token) <*>> lengthed_list 2 token))

  export
  with_id : (Cons (Posed Bits8) i, Monoid i) => {type : HandshakeType} -> Parserializer Bits8 i (SimpleError String) (Handshake type) -> Parserializer Bits8 i (SimpleError String) (Handshake type)
  with_id pser = under (show type <+> " handshake") $ is (to_vect $ handshake_type_to_id type) *> pser

  export
  handshake : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (DPair _ Handshake)
  handshake = map fix_handshake hack_handshake
    $ (with_id no_id_client_hello)
    <|> (with_id no_id_server_hello)
    <|> (with_id no_id_encrypted_extensions)
    <|> (with_id no_id_certificate)
    <|> (with_id no_id_certificate_verify)
    <|> (with_id no_id_finished)
    <|> (with_id no_id_new_session_ticket)

  export
  handshake2 : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (DPair _ Handshake)
  handshake2 = map fix_handshake hack_handshake
    $ (with_id no_id_client_hello)
    <|> (with_id no_id_server_hello)
    <|> (with_id no_id_encrypted_extensions)
    <|> (with_id no_id_certificate2)
    <|> (with_id no_id_certificate_verify)
    <|> (with_id no_id_finished)
    <|> (with_id no_id_new_session_ticket)

