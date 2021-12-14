module Network.TLS.HelloExtension

import Data.List1
import Data.Vect
import Network.TLS.Magic
import Network.TLS.Parsing
import Utils.Bytes
import Utils.Misc
import Utils.Show

public export
KeyBytes : Type
KeyBytes = List Bits8

-- TODO: even more stuff
public export
data ServerNameEntry : Type where
  DNS : String -> ServerNameEntry

public export
Show ServerNameEntry where
  show (DNS x) = show_record "DNS" [("name", show x)]

XServerNameEntry : Type
XServerNameEntry = Eithers [String]

hack_server_name_entry : ServerNameEntry -> XServerNameEntry
hack_server_name_entry (DNS x) = x

fix_server_name_entry : XServerNameEntry -> ServerNameEntry
fix_server_name_entry x = (DNS x)

namespace ClientExtension
  public export
  data ClientExtension : ExtensionType -> Type where
    ServerName : List1 ServerNameEntry -> ClientExtension ServerName
    SupportedGroups : List1 SupportedGroup -> ClientExtension SupportedGroups
    SignatureAlgorithms : List1 SignatureAlgorithm -> ClientExtension SignatureAlgorithms
    SupportedVersions : List1 TLSVersion -> ClientExtension SupportedVersions
    KeyShare : List1 (SupportedGroup, KeyBytes) -> ClientExtension KeyShare
    -- TODO: PSK

  public export
  Show (ClientExtension type) where
    show (ServerName entries) = show_record "ServerName" [("entries", show entries)]
    show (SupportedGroups entries) = show_record "SupportedGroups" [("entries", show entries)]
    show (SignatureAlgorithms entries) = show_record "SignatureAlgorithms" [("entries", show entries)]
    show (SupportedVersions entries) = show_record "SupportedVersions" [("entries", show entries)]
    show (KeyShare entries) = show_record "KeyShare" [("entries", show entries)]

XClientExtension : Type
XClientExtension = Eithers
  [ ClientExtension ServerName
  , ClientExtension SupportedGroups
  , ClientExtension SignatureAlgorithms
  , ClientExtension SupportedVersions
  , ClientExtension KeyShare
  ]

hack_client_extension : DPair _ ClientExtension -> XClientExtension
hack_client_extension (ServerName ** x) = Left x
hack_client_extension (SupportedGroups ** x) = Right (Left x)
hack_client_extension (SignatureAlgorithms ** x) = Right (Right (Left x))
hack_client_extension (SupportedVersions ** x) = Right (Right (Right (Left x)))
hack_client_extension (KeyShare ** x) = Right (Right (Right (Right x)))

fix_client_extension : XClientExtension -> DPair _ ClientExtension
fix_client_extension (Left x) = (_ ** x)
fix_client_extension (Right (Left x)) = (_ ** x)
fix_client_extension (Right (Right (Left x))) = (_ ** x)
fix_client_extension (Right (Right (Right (Left x)))) = (_ ** x)
fix_client_extension (Right (Right (Right (Right x)))) = (_ ** x)

namespace ServerExtension
  public export
  data ServerExtension : ExtensionType -> Type where
    SupportedGroups : SupportedGroup -> ServerExtension SupportedGroups
    SignatureAlgorithms : SignatureAlgorithm -> ServerExtension SignatureAlgorithms
    SupportedVersions : TLSVersion -> ServerExtension SupportedVersions
    KeyShare : (SupportedGroup, KeyBytes) -> ServerExtension KeyShare
    Unknown : (id : (Bits8, Bits8)) -> List Bits8 -> ServerExtension (Unknown id)

  public export
  Show (ServerExtension type) where
    show (SupportedGroups entries) = show_record "SupportedGroups" [("entry", show entries)]
    show (SignatureAlgorithms entries) = show_record "SignatureAlgorithms" [("entry", show entries)]
    show (SupportedVersions entries) = show_record "SupportedVersions" [("entry", show entries)]
    show (KeyShare entries) = show_record "KeyShare" [("entry", show entries)]
    show (Unknown (a, b) body) = show_record "Unknown" [("id", xxd [a, b]), ("body", xxd body)]

XServerExtension : Type
XServerExtension = Eithers
  [ ServerExtension SupportedGroups
  , ServerExtension SignatureAlgorithms
  , ServerExtension SupportedVersions
  , ServerExtension KeyShare
  , (a ** ServerExtension (Unknown a))
  ]

hack_server_extension : DPair _ ServerExtension -> XServerExtension
hack_server_extension (SupportedGroups ** x)     = Left x
hack_server_extension (SignatureAlgorithms ** x) = Right (Left x)
hack_server_extension (SupportedVersions ** x)   = Right (Right (Left x))
hack_server_extension (KeyShare ** x)            = Right (Right (Right (Left x)))
hack_server_extension ((Unknown id) ** x)        = Right (Right (Right (Right (id ** x))))

fix_server_extension : XServerExtension -> DPair _ ServerExtension
fix_server_extension (Left x) = (_ ** x)
fix_server_extension (Right (Left x)) = (_ ** x)
fix_server_extension (Right (Right (Left x))) = (_ ** x)
fix_server_extension (Right (Right (Right (Left x)))) = (_ ** x)
fix_server_extension (Right (Right (Right (Right (x ** y))))) = (_ ** y)

namespace Parsing
  namespace Client
    export
    with_id : (Cons (Posed Bits8) i, Monoid i) => {type : ExtensionType} -> Parserializer Bits8 i (SimpleError String) (ClientExtension type) -> Parserializer Bits8 i (SimpleError String) (ClientExtension type)
    with_id pser = under (show type <+> " extension") $ is (pair_to_vect $ extension_type_to_id type) *> pser

    -- TODO: generalize
    export
    server_name_dns_entry : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) String
    server_name_dns_entry = is [0x00] *> map ascii_to_string string_to_ascii (lengthed_list 2 token)

    export
    server_name_entry : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) ServerNameEntry
    server_name_entry = map fix_server_name_entry hack_server_name_entry $ server_name_dns_entry

    export
    no_id_server_name : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (ClientExtension ServerName)
    no_id_server_name = lengthed 2 $ map ServerName (\(ServerName x) => x) $ lengthed_list1 2 server_name_entry

    export
    no_id_supported_groups : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (ClientExtension SupportedGroups)
    no_id_supported_groups = lengthed 2 $ map SupportedGroups (\(SupportedGroups x) => x) $ lengthed_list1 2 supported_group

    export
    no_id_signature_algorithms : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (ClientExtension SignatureAlgorithms)
    no_id_signature_algorithms = lengthed 2 $ map SignatureAlgorithms (\(SignatureAlgorithms x) => x) $ lengthed_list1 2 signature_algorithm

    export
    no_id_supported_versions : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (ClientExtension SupportedVersions)
    no_id_supported_versions = lengthed 2 $ map SupportedVersions (\(SupportedVersions x) => x) $ lengthed_list1 1 tls_version

    export
    no_id_key_share : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (ClientExtension KeyShare)
    no_id_key_share = lengthed 2 $ map KeyShare (\(KeyShare x) => x) $ lengthed_list1 2 (supported_group <*>> lengthed_list 2 token)

    export
    extension : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (DPair _ ClientExtension)
    extension = map fix_client_extension hack_client_extension
      $ (with_id no_id_server_name)
      <|> (with_id no_id_supported_groups)
      <|> (with_id no_id_signature_algorithms)
      <|> (with_id no_id_supported_versions)
      <|> (with_id no_id_key_share)

  namespace Server
    export
    no_id_supported_groups : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (ServerExtension SupportedGroups)
    no_id_supported_groups = lengthed 2 $ map SupportedGroups (\(SupportedGroups x) => x) $ supported_group

    export
    no_id_signature_algorithms : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (ServerExtension SignatureAlgorithms)
    no_id_signature_algorithms = lengthed 2 $ map SignatureAlgorithms (\(SignatureAlgorithms x) => x) $ signature_algorithm

    export
    no_id_supported_versions : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (ServerExtension SupportedVersions)
    no_id_supported_versions = lengthed 2 $ map SupportedVersions (\(SupportedVersions x) => x) $ tls_version

    export
    no_id_key_share : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (ServerExtension KeyShare)
    no_id_key_share = lengthed 2 $ map KeyShare (\(KeyShare x) => x) $ (supported_group <*>> lengthed_list 2 token)

    export
    with_id : (Cons (Posed Bits8) i, Monoid i) => {type : ExtensionType} -> Parserializer Bits8 i (SimpleError String) (ServerExtension type) -> Parserializer Bits8 i (SimpleError String) (ServerExtension type)
    with_id pser = under (show type <+> " extension") $ is (pair_to_vect $ extension_type_to_id type) *> pser

    export
    with_id_unknown : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (rid ** ServerExtension (Unknown rid))
    with_id_unknown = MkParserializer serialize deserialize
      where
        serialize : (rid ** ServerExtension (Unknown rid)) -> List Bits8
        serialize ((a,b) ** (Unknown _ body)) = [a,b] <+> (prepend_length 2 body)
        deserialize : Parser i (SimpleError String) (rid ** ServerExtension (Unknown rid))
        deserialize = do
          [a, b] <- count 2 p_get
          body <- (lengthed_list 2 token).decode
          pure ((a,b) ** Unknown (a,b) body)

    export
    extension : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (DPair _ ServerExtension)
    extension = map fix_server_extension hack_server_extension
      $ (with_id no_id_supported_groups)
      <|> (with_id no_id_signature_algorithms)
      <|> (with_id no_id_supported_versions)
      <|> (with_id no_id_key_share)
      <|> (with_id_unknown)

