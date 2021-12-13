module Data.Security.DER

import Data.Bits
import Data.Vect
import Utils.Bytes

-- TODO: implementation

public export
data RecordLength : Type where
  Variable : RecordLength
  Fixed : Nat -> RecordLength

public export
data Tag : Type where
  TagImplicit        : Tag
  TagBoolean         : Tag
  TagInteger         : Tag
  TagBitString       : Tag
  TagOctetString     : Tag
  TagNull            : Tag
  TagObjectID        : Tag
  TagUtf8String      : Tag
  TagSequence        : Tag
  TagSet             : Tag
  TagPrintableString : Tag
  TagT61String       : Tag
  TagIA5String       : Tag
  TagUtcTime         : Tag
  TagHigh            : Tag

public export
Show Tag where
  show TagImplicit        = "IMPLICIT"
  show TagBoolean         = "BOOLEAN"
  show TagInteger         = "INTEGER"
  show TagBitString       = "BIT_STRING"
  show TagOctetString     = "OCTET_STRING"
  show TagNull            = "NULL"
  show TagObjectID        = "OBJECT_ID"
  show TagUtf8String      = "UTF8_STRING"
  show TagSequence        = "SEQUENCE"
  show TagSet             = "SET"
  show TagPrintableString = "PRINTABLE_STRING"
  show TagT61String       = "T61_STRING"
  show TagIA5String       = "IA5_STRING"
  show TagUtcTime         = "UTCTIME"
  show TagHigh            = "<high tag>"

public export
tag_to_id : Tag -> Bits8
tag_to_id TagImplicit        = 0x00
tag_to_id TagBoolean         = 0x01
tag_to_id TagInteger         = 0x02
tag_to_id TagBitString       = 0x03
tag_to_id TagOctetString     = 0x04
tag_to_id TagNull            = 0x05
tag_to_id TagObjectID        = 0x06
tag_to_id TagUtf8String      = 0x0c
tag_to_id TagSequence        = 0x10
tag_to_id TagSet             = 0x11
tag_to_id TagPrintableString = 0x13
tag_to_id TagT61String       = 0X14
tag_to_id TagIA5String       = 0X16
tag_to_id TagUtcTime         = 0X17
tag_to_id TagHigh            = 0x1f

public export
id_to_tag : Bits8 -> Maybe Tag
id_to_tag 0x00 = Just TagImplicit
id_to_tag 0x01 = Just TagBoolean
id_to_tag 0x02 = Just TagInteger
id_to_tag 0x03 = Just TagBitString
id_to_tag 0x04 = Just TagOctetString
id_to_tag 0x05 = Just TagNull
id_to_tag 0x06 = Just TagObjectID
id_to_tag 0x0c = Just TagUtf8String
id_to_tag 0x10 = Just TagSequence
id_to_tag 0x11 = Just TagSet
id_to_tag 0x13 = Just TagPrintableString
id_to_tag 0X14 = Just TagT61String
id_to_tag 0X16 = Just TagIA5String
id_to_tag 0X17 = Just TagUtcTime
id_to_tag 0x1f = Just TagHigh
id_to_tag _    = Nothing
