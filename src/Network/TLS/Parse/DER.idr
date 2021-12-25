module Network.TLS.Parse.DER

import Data.List1
import Data.Bits
import Data.Vect
import Utils.Bytes
import Utils.Parser
import Network.TLS.Parsing
import Utils.Misc

import Debug.Trace

public export
data TagType : Type where
  Universal : TagType
  Application : TagType
  ContextSpecific : TagType
  Private : TagType

public export
Show TagType where
  show Universal       = "Universal"
  show Application     = "Application"
  show ContextSpecific = "ContextSpecific"
  show Private         = "Private"

public export
record Tag where
  constructor MkTag
  type : TagType
  tag_id : Nat

public export
Show Tag where
  show tag = "(" <+> show tag.type <+> ", " <+> show tag.tag_id <+> ")"

export
is_constructed : Bits8 -> Bool
is_constructed tag = testBit tag 5

export
record BitArray where
  constructor MkBitArray
  padding : Nat
  bytes : List Bits8

export
record Certificate where
  version : Nat
  serial_number : Integer

public export
data ASN1 : TagType -> Nat -> Type where
  Boolean : Bool -> ASN1 Universal 0x01
  IntVal : Integer -> ASN1 Universal 0x02
  Bitstring : BitArray -> ASN1 Universal 0x03
  OctetString : List Bits8 -> ASN1 Universal 0x04
  Null : ASN1 Universal 0x05
  OID : List Nat -> ASN1 Universal 0x06
  PrintableString : String -> ASN1 Universal 0x13
  Sequence : List (t ** n ** ASN1 t n) -> ASN1 Universal 0x10 -- 0x30 & 31
  Set : List (t ** n ** ASN1 t n) -> ASN1 Universal 0x11 -- 0x31 & 31
  UnknownConstructed : (t : TagType) -> (n : Nat) -> List (t ** n ** ASN1 t n) -> ASN1 t n
  UnknownPrimitive : (t : TagType) -> (n : Nat) -> List Bits8 -> ASN1 t n

public export
Eq BitArray where
  (MkBitArray a b) == (MkBitArray c d) = (a == c) && (b == d)

export
constraint_parse : (Cons (Posed Bits8) i, Monoid i) => (n : Nat) ->
                   (pser : Parser i (SimpleError String) a) ->
                   Parser i (SimpleError String) (List a)
constraint_parse Z pser = pure []
constraint_parse (S len) pser = go (S len) pser
  where
  go : Nat -> Parser i (SimpleError String) a -> Parser i (SimpleError String) (List a)
  go Z (Pure leftover x) = pure [x]
  go (S i) (Pure leftover x) = (x ::) <$> go (S i) pser
  go i (Fail msg) = fail msg
  go Z parser = fail $ msg $ "under fed, want more"
  go (S i) parser = do
    b <- token
    go i (feed (singleton b) parser)

parse_length : (Monoid i, Cons (Posed Bits8) i) => Parser i (SimpleError String) Nat
parse_length = do
  b <- p_get
  let b' = b .&. 0x7F
  if b' == b
     then pure $ cast b
     else p_nat (cast b')

extract_tag_type_bits : Bits8 -> TagType
extract_tag_type_bits x =
  case get_bits x of
    [ False, False ] => Universal
    [ False, True  ] => Application
    [ True,  False ] => ContextSpecific
    [ True,  True  ] => Private
  where
    get_bits : Bits8 -> Vect 2 Bool
    get_bits x = [ (testBit x 7), (testBit x 6) ]

parse_tag_id : (Monoid i, Cons (Posed Bits8) i) => Parser i (SimpleError String) (Bool, Tag)
parse_tag_id = do
  b <- p_get
  let construct = is_constructed b
  let type = extract_tag_type_bits b
  let id = b .&. 31
  if id == 31
    then (\x => (construct, MkTag type x)) <$> parse_length
    else pure (construct, MkTag type $ cast id)

export
signed_be_to_integer : List1 Bits8 -> Integer
signed_be_to_integer l@(x ::: xs) =
  let is_neg = testBit x 7
      v = be_to_integer l
      m = (shiftL 1 (8 * (length l))) - 1 -- 2^n - 1
  in if is_neg then v .|. (complement m) else v

export
decode_oid_nodes : Bits8 -> List Bits8 -> List Nat
decode_oid_nodes first_node nodes =
  let a = first_node `div` 40
      b = first_node `mod` 40
      (_, result) = foldl go (0, []) nodes
      nodes = cast a :: cast b :: reverse result
  in integerToNat <$> nodes
  where
    go : (Integer, List Integer) -> Bits8 -> (Integer, List Integer)
    go (value, result) byte =
      let value = (shiftL value 7) .|. cast (byte .&. 0x7F)
      in if byte >= 0x80 then (value, result) else (0, value :: result)

export
parse_boolean : (Cons (Posed Bits8) i, Monoid i) => Nat -> Parser i (SimpleError String) Bool
parse_boolean 1 = map (/= 0) p_get
parse_boolean n = fail $ msg $ "boolean length should be 1, got: " <+> show n

export
parse_integer : (Cons (Posed Bits8) i, Monoid i) => Nat -> Parser i (SimpleError String) Integer
parse_integer n = do
  bits <- count n p_get
  case fromList $ toList bits of
    Just x => pure $ signed_be_to_integer x
    Nothing => fail $ msg "integer length is 0"

export
parse_bitarray : (Cons (Posed Bits8) i, Monoid i) => Nat -> Parser i (SimpleError String) BitArray
parse_bitarray Z = fail $ msg "bitarray length is 0"
parse_bitarray (S n) = do
  pad_len <- p_get
  bits <- toList <$> count n p_get
  pure $ MkBitArray (cast pad_len) bits

export
parse_null : (Cons (Posed Bits8) i, Monoid i) => Nat -> Parser i (SimpleError String) ()
parse_null Z = pure ()
parse_null n = fail $ msg $ "null length should be 0, got: " <+> show n

export
parse_oid : (Cons (Posed Bits8) i, Monoid i) => Nat -> Parser i (SimpleError String) (List Nat)
parse_oid Z = fail $ msg "oid length is 0"
parse_oid (S n) = do
  first_node <- p_get
  nodes <- toList <$> count n p_get
  pure $ decode_oid_nodes first_node nodes

public export
ASN1Token : Type
ASN1Token = (t ** n ** ASN1 t n)

export
parse_asn1 : (Monoid i, Cons (Posed Bits8) i) => Parser i (SimpleError String) ASN1Token
parse_asn1 = do
  tag' <- parse_tag_id
  len <- parse_length
  case tag' of
    (False, MkTag Universal 1) => (\b => (Universal ** 1 ** Boolean b)) <$> parse_boolean len
    (False, MkTag Universal 2) => (\b => (Universal ** 2 ** IntVal b)) <$> parse_integer len
    (False, MkTag Universal 3) => (\b => (Universal ** 3 ** Bitstring b)) <$> parse_bitarray len
    (False, MkTag Universal 4) => (\b => (Universal ** 4 ** OctetString $ toList b)) <$> count len p_get
    (False, MkTag Universal 5) => (\b => (Universal ** 5 ** Null)) <$> parse_null len
    (False, MkTag Universal 6) => (\b => (Universal ** 6 ** OID b)) <$> parse_oid len
    (False, MkTag Universal 19) => (\b => (Universal ** 19 ** PrintableString $ ascii_to_string $ toList b)) <$> count len p_get
    (True,  MkTag Universal 16) => (\b => (Universal ** 16 ** Sequence b)) <$> constraint_parse len parse_asn1
    (True,  MkTag Universal 17) => (\b => (Universal ** 17 ** Set b)) <$> constraint_parse len parse_asn1
    (True,  MkTag t n) => (\b => (t ** n ** UnknownConstructed t n b)) <$> constraint_parse len parse_asn1
    (False, MkTag t n) => (\b => (t ** n ** UnknownPrimitive t n $ toList b)) <$> count len p_get
