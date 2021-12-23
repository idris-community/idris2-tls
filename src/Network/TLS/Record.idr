module Network.TLS.Record

import Utils.Bytes
import Utils.Misc
import Utils.Show
import Data.Vect
import public Network.TLS.HelloExtension
import public Network.TLS.Handshake
import public Network.TLS.Magic
import public Network.TLS.Parsing
import public Network.TLS.Wrapper

public export
data Record : RecordType -> Type where
  ChangeCipherSpec : (body : List Bits8) -> Record ChangeCipherSpec
  Handshake : (handshakes : List (DPair _ Handshake)) -> Record Handshake
  ApplicationData : (body : List Bits8) -> Record ApplicationData
  Alert : (AlertLevel, AlertDescription) -> Record Alert

public export
Show (Record type) where
  show (ChangeCipherSpec body) = show_record "ChangeCipherSpec"
    [ ("body", xxd body)
    ]
  show (Handshake handshakes) = show_record "Handshake"
    [ ("handshakes", show (map (\x => show x.snd) handshakes))
    ]
  show (ApplicationData body) = show_record "ApplicationData"
    [ ("body", xxd body)
    ]
  show (Alert (lvl, desc)) = show_record "Alert"
    [ ("alert_level", show lvl)
    , ("alert", show desc)
    ]

XRecord : Type
XRecord = Eithers [Record ChangeCipherSpec, Record Handshake, Record ApplicationData, Record Alert]

hack_record : DPair _ Record -> XRecord
hack_record (ChangeCipherSpec ** x) = Left x
hack_record (Handshake ** x)        = Right (Left x)
hack_record (ApplicationData  ** x) = Right (Right (Left x))
hack_record (Alert ** x)            = Right (Right (Right x))

fix_record : XRecord -> DPair _ Record
fix_record (Left x)                  = (ChangeCipherSpec ** x)
fix_record (Right (Left x))          = (Handshake ** x)
fix_record (Right (Right (Left x)))  = (ApplicationData ** x)
fix_record (Right (Right (Right x))) = (Alert ** x)

XRecordWithVersion : Type
XRecordWithVersion = Eithers
  [ (TLSVersion, Record ChangeCipherSpec)
  , (TLSVersion, Record Handshake)
  , (TLSVersion, Record ApplicationData)
  , (TLSVersion, Record Alert)
  ]

hack_record_with_version : (TLSVersion, DPair _ Record) -> XRecordWithVersion
hack_record_with_version (v, (ChangeCipherSpec ** x)) = Left (v, x)
hack_record_with_version (v, (Handshake ** x))        = Right (Left (v, x))
hack_record_with_version (v, (ApplicationData  ** x)) = Right (Right (Left (v, x)))
hack_record_with_version (v, (Alert ** x))            = Right (Right (Right (v, x)))

fix_record_with_version : XRecordWithVersion -> (TLSVersion, DPair _ Record)
fix_record_with_version (Left (v, x))                  = (v, (ChangeCipherSpec ** x))
fix_record_with_version (Right (Left (v, x)))          = (v, (Handshake ** x))
fix_record_with_version (Right (Right (Left (v, x))))  = (v, (ApplicationData ** x))
fix_record_with_version (Right (Right (Right (v, x)))) = (v, (Alert ** x))

namespace Parsing
  export
  no_id_change_cipher_spec : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Record ChangeCipherSpec)
  no_id_change_cipher_spec = map (\a => ChangeCipherSpec a) (\(ChangeCipherSpec a) => a)
    $ lengthed_list 2 token

  export
  no_id_handshake : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Record Handshake)
  no_id_handshake = map (\a => Handshake a) (\(Handshake a) => a)
    $ lengthed_list 2 handshake

  export
  no_id_handshake2 : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Record Handshake)
  no_id_handshake2 = map (\a => Handshake a) (\(Handshake a) => a)
    $ lengthed_list 2 handshake2

  export
  no_id_application_data : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Record ApplicationData)
  no_id_application_data = map (\a => ApplicationData a) (\(ApplicationData a) => a)
    $ lengthed_list 2 token

  export
  record_type_with_version : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (RecordType, TLSVersion)
  record_type_with_version = record_type <*>> tls_version

  export
  record_type_with_version_with_length : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (RecordType, TLSVersion, Nat)
  record_type_with_version_with_length = record_type <*>> tls_version <*>> nat 2

  export
  alert : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (AlertLevel, AlertDescription)
  alert = under "alert protocol" $ alert_level <*>> alert_description

  export
  no_id_alert : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Record Alert)
  no_id_alert = map (\((), a) => Alert a) (\(Alert a) => ((), a)) $ is [0x00, 0x02] <*>> alert

  export
  with_id_with_version : (Cons (Posed Bits8) i, Monoid i) => {type : RecordType} -> Parserializer Bits8 i (SimpleError String) (Record type) -> Parserializer Bits8 i (SimpleError String) (TLSVersion, Record type)
  with_id_with_version pser = under (show type <+> " record") $ is (to_vect $ record_type_to_id type) *> (tls_version <*>> pser)

  export
  arecord : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (TLSVersion, DPair _ Record)
  arecord =
    map fix_record_with_version hack_record_with_version
    $ (with_id_with_version no_id_change_cipher_spec)
    <|> (with_id_with_version no_id_handshake)
    <|> (with_id_with_version no_id_application_data)
    <|> (with_id_with_version no_id_alert)

  export
  arecord2 : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (TLSVersion, DPair _ Record)
  arecord2 =
    map fix_record_with_version hack_record_with_version
    $ (with_id_with_version no_id_change_cipher_spec)
    <|> (with_id_with_version no_id_handshake2)
    <|> (with_id_with_version no_id_application_data)
    <|> (with_id_with_version no_id_alert)

  export
  alert_or_arecord : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Either (AlertLevel, AlertDescription) (TLSVersion, DPair _ Record))
  alert_or_arecord = alert <|> arecord

  export
  alert_or_arecord2 : (Cons (Posed Bits8) i, Monoid i) => Parserializer Bits8 i (SimpleError String) (Either (AlertLevel, AlertDescription) (TLSVersion, DPair _ Record))
  alert_or_arecord2 = alert <|> arecord2

  export
  wrapper2 : (Cons (Posed Bits8) i, Monoid i) => {iv_size : Nat} -> {mac_size : Nat} -> Parserializer Bits8 i (SimpleError String) (RecordType, TLSVersion, Wrapper2 iv_size mac_size)
  wrapper2 =
    record_type
    <*>> tls_version
    <*>> (mapEither (\x => maybe_to_either (from_application_data2 x) (msg "cannot parse wrapper")) to_application_data2 $ lengthed_list 2 token)
