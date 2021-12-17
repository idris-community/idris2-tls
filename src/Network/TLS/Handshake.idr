module Network.TLS.Handshake

import Data.Either
import Data.List1
import Data.Vect
import Network.TLS.HelloExtension
import Network.TLS.Magic
import Network.TLS.Parsing
import Utils.Bytes
import Utils.Misc
import Utils.Show

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
  record CertificateEntry where
    constructor MkCertificateEntry
    body : List Bits8
    extensions : List Bits8

  public export
  Show CertificateEntry where
    show x = show_record "CertificateEntry"
      [ ("certificate", show $ xxd $ x.body)
      , ("certificate_extension", xxd x.extensions)
      ]

  public export
  record Certificate where
    constructor MkCertificate
    request_context : List Bits8
    certificates : List CertificateEntry

  public export
  Show Certificate where
    show x = show_record "Certificate"
      [ ("request_context", xxd x.request_context)
      , ("certificates", foldl (<+>) "" $ map show $ x.certificates)
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
  record ServerKeyExchange where
    constructor MkServerKeyExchange
    server_pk_group : SupportedGroup
    server_pk_body : List Bits8
    signature_algo : SignatureAlgorithm
    signature_body : List Bits8

  public export
  Show ServerKeyExchange where
    show x = show_record "ServerKeyExchange"
      [ ("server_pk_group", show x.server_pk_group)
      , ("server_pk_body", xxd x.server_pk_body)
      , ("signature_algo", show x.signature_algo)
      , ("signature_body", xxd x.signature_body)
      ]

  public export
  record ServerHelloDone where
    constructor MkServerHelloDone

  public export
  Show ServerHelloDone where
    show x = show_record "ServerHelloDone" []

  public export
  record ClientKeyExchange where
    constructor MkClientKeyExchange
    public_key : List Bits8

  Show ClientKeyExchange where
    show x = show_record "ClientKeyExchange" 
      [ ("public_key", show x.public_key)
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
  ServerKeyExchange : ServerKeyExchange -> Handshake ServerKeyExchange
  ServerHelloDone : ServerHelloDone -> Handshake ServerHelloDone
  ClientKeyExchange : ClientKeyExchange -> Handshake ClientKeyExchange

public export
Show (Handshake type) where
  show (ClientHello x) = show x
  show (ServerHello x) = show x
  show (EncryptedExtensions x) = show x
  show (Certificate x) = show x
  show (CertificateVerify x) = show x
  show (Finished x) = show x
  show (NewSessionTicket x) = show x
  show (ServerKeyExchange x) = show x
  show (ServerHelloDone x) = show x
  show (ClientKeyExchange x) = show x

XHandshake : Type
XHandshake = Eithers 
  [ Handshake ClientHello
  , Handshake ServerHello
  , Handshake EncryptedExtensions
  , Handshake Certificate
  , Handshake CertificateVerify
  , Handshake Finished
  , Handshake NewSessionTicket
  , Handshake ServerKeyExchange
  , Handshake ServerHelloDone
  , Handshake ClientKeyExchange
  ]

hack_handshake : DPair _ Handshake -> XHandshake
hack_handshake (ClientHello ** x)         = Left x
hack_handshake (ServerHello ** x)         = Right (Left x)
hack_handshake (EncryptedExtensions ** x) = Right (Right (Left x))
hack_handshake (Certificate ** x)         = Right (Right (Right (Left x)))
hack_handshake (CertificateVerify ** x)   = Right (Right (Right (Right (Left x))))
hack_handshake (Finished ** x)            = Right (Right (Right (Right (Right (Left x)))))
hack_handshake (NewSessionTicket ** x)    = Right (Right (Right (Right (Right (Right (Left x))))))
hack_handshake (ServerKeyExchange ** x)   = Right (Right (Right (Right (Right (Right (Right (Left x)))))))
hack_handshake (ServerHelloDone ** x)     = Right (Right (Right (Right (Right (Right (Right (Right (Left x))))))))
hack_handshake (ClientKeyExchange ** x)   = Right (Right (Right (Right (Right (Right (Right (Right (Right x))))))))

fix_handshake : XHandshake -> DPair _ Handshake
fix_handshake (Left x)                                                                  = (ClientHello ** x)
fix_handshake (Right (Left x))                                                          = (ServerHello ** x)
fix_handshake (Right (Right (Left x)))                                                  = (EncryptedExtensions ** x)
fix_handshake (Right (Right (Right (Left x))))                                          = (Certificate ** x)
fix_handshake (Right (Right (Right (Right (Left x)))))                                  = (CertificateVerify ** x)
fix_handshake (Right (Right (Right (Right (Right (Left x))))))                          = (Finished ** x)
fix_handshake (Right (Right (Right (Right (Right (Right (Left x)))))))                  = (NewSessionTicket ** x)
fix_handshake (Right (Right (Right (Right (Right (Right (Right (Left x))))))))          = (ServerKeyExchange ** x)
fix_handshake (Right (Right (Right (Right (Right (Right (Right (Right (Left x)))))))))  = (ServerHelloDone ** x)
fix_handshake (Right (Right (Right (Right (Right (Right (Right (Right (Right x))))))))) = (ClientKeyExchange ** x)

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
  no_id_server_hello = map
    ((\(a,b,c,d,e,f) => ServerHello (MkServerHello a b c d e f)) . fromEither) -- (\(a,b,c,d,e,f) => ServerHello (MkServerHello a b c d e f))
    (\(ServerHello (MkServerHello a b c d e f)) => Left (a,b,c,d,e,f))
    $ ( lengthed 3
    $ (under "server version" tls_version)
    <*>> (under "server random" $ ntokens 32)
    <*>> (under "session id" $ lengthed_list 1 token)
    <*>> (under "server chosen cipher suite" $ cipher_suite)
    <*>> (under "server chosen compression level" $ compression_level)
    <*>> (under "server extensions" $ lengthed_list 2 Server.extension)
    )
    <|> ( lengthed 3
    $ (under "server version" tls_version)
    <*>> (under "server random" $ ntokens 32)
    <*>> (under "session id" $ lengthed_list 1 token)
    <*>> (under "server chosen cipher suite" $ cipher_suite)
    <*>> (under "server chosen compression level" $ compression_level)
    <*>> (under "server extensions" $ MkParserializer (const []) (pure []))
    )

  export
  no_id_encrypted_extensions : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake EncryptedExtensions)
  no_id_encrypted_extensions = map (\a => EncryptedExtensions (MkEncryptedExtensions a)) (\(EncryptedExtensions (MkEncryptedExtensions a)) => a)
    $ lengthed 3
    $ (under "encrypted extensions body" $ lengthed_list 2 token)

  export
  no_id_certificate : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake Certificate)
  no_id_certificate =
    map
    (\(a,b) => Certificate (MkCertificate a $ map (uncurry MkCertificateEntry) b))
    (\(Certificate (MkCertificate a d)) => (a, map (\b => (b.body, b.extensions)) d))
    $ lengthed 3
    $ (under "request context" $ lengthed_list 1 token)
    <*>> (under "certificates"
         $ under "certificate list"
         $ lengthed_list 3
         $ under "certificate entry"
         $ (lengthed_list 3 token <*>> (under "certificate extensions" $ lengthed_list 2 token)))

  export
  no_id_certificate2 : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake Certificate)
  no_id_certificate2 = map
    (\b => Certificate (MkCertificate [] $ map (\x => MkCertificateEntry x []) b))
    (\(Certificate (MkCertificate a b)) => map body b)
    $ lengthed 3
    $ (under "certificate list 1.2" $ lengthed_list 3 $ under "certificate entry 1.2" $ lengthed_list 3 token)

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
  no_id_new_session_ticket = map
    (\(a,b,c,d,e) => NewSessionTicket (MkNewSessionTicket a b c d e))
    (\(NewSessionTicket (MkNewSessionTicket a b c d e)) => (a,b,c,d,e))
    $ lengthed 3
    $ (under "ticket lifetime seconds" $ nat 4)
    <*>> (under "ticket age add milliseconds" $ nat 4)
    <*>> (under "ticket nonce" $ lengthed_list 1 token)
    <*>> (under "session ticket" $ lengthed_list 2 token)
    <*>> (under "extensions" $ lengthed_list 2 ((token <*>> token) <*>> lengthed_list 2 token))

  export
  no_id_server_key_exchange : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake ServerKeyExchange)
  no_id_server_key_exchange = map
    (\(a,b,c,d) => ServerKeyExchange (MkServerKeyExchange a b c d))
    (\(ServerKeyExchange (MkServerKeyExchange a b c d)) => (a,b,c,d))
    $ lengthed 3
    $ (under "curve info" $ (is [0x03]) *> supported_group)
    <*>> (under "public key" $ lengthed_list 1 token)
    <*>> (under "signature algo" signature_algorithm)
    <*>> (under "signature body" $ lengthed_list 2 token)

  export
  no_id_server_hello_done : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake ServerHelloDone)
  no_id_server_hello_done = map
    (const (ServerHelloDone MkServerHelloDone))
    (const ())
    $ is [0x00, 0x00, 0x00]

  export
  no_id_client_key_exchange : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Handshake ClientKeyExchange)
  no_id_client_key_exchange = map
    (ClientKeyExchange . MkClientKeyExchange)
    (\(ClientKeyExchange (MkClientKeyExchange x)) => x)
    $ lengthed 3
    $ (under "public key" $ lengthed_list 1 token)

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
    <|> (with_id no_id_server_key_exchange)
    <|> (with_id no_id_server_hello_done)
    <|> (with_id no_id_client_key_exchange)

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
    <|> (with_id no_id_server_key_exchange)
    <|> (with_id no_id_server_hello_done)
    <|> (with_id no_id_client_key_exchange)
