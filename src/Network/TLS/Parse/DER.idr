module Network.TLS.Parse.DER

import Data.List1
import Data.Bits
import Data.Vect
import Utils.Bytes
import Utils.Parser
import Network.TLS.Parsing

export
record Bitstring where
  constructor MkBitstring
  padding : Nat
  bytes : List Bits8

public export
Eq Bitstring where
  (MkBitstring a b) == (MkBitstring c d) = (a == c) && (b == d)

export
parse_length : (Monoid i, Cons (Posed Bits8) i) => Parser i (SimpleError String) Nat
parse_length = do
  b <- p_get
  let b' = b .&. 0x7F
  if b' == b
     then pure $ cast b
     else p_nat (cast b')

export
parse_tl : (Cons (Posed Bits8) i, Monoid i) => Bits8 -> Parser i (SimpleError String) Nat
parse_tl tag = do
  tag' <- p_get
  if tag' == tag
     then parse_length
     else fail $ msg $ "expected tag " <+> show_hex tag <+> " , got: " <+> show_hex tag'

export
parse_tlv : (Cons (Posed Bits8) i, Monoid i) => Bits8 -> (p : Parser i (SimpleError String) a) -> Parser i (SimpleError String) a
parse_tlv tag p = parse_tl tag >>= (flip p_exact) p

export
parse_sequence : (Cons (Posed Bits8) i, Monoid i) => (p : Parser i (SimpleError String) a) -> Parser i (SimpleError String) a
parse_sequence = parse_tlv 0x30

export
signed_be_to_integer : List1 Bits8 -> Integer
signed_be_to_integer l@(x ::: xs) =
  let is_neg = testBit x 7
      v = be_to_integer l
      m = (shiftL 1 (8 * (length l))) - 1 -- 2^n - 1
  in if is_neg then v .|. (complement m) else v

export
decode_oid_nodes : Bits8 -> List Bits8 -> List Integer
decode_oid_nodes first_node nodes =
  let a = first_node `div` 40
      b = first_node `mod` 40
      (_, result) = foldl go (0, []) nodes
  in cast a :: cast b :: reverse result
  where
    go : (Integer, List Integer) -> Bits8 -> (Integer, List Integer)
    go (value, result) byte =
      let value = (shiftL value 7) .|. cast (byte .&. 0x7F)
      in if byte >= 0x80 then (value, result) else (0, value :: result)

export
parse_boolean : (Cons (Posed Bits8) i, Monoid i) => Parser i (SimpleError String) Bool
parse_boolean = do
  1 <- parse_tl 0x01
  | other => fail $ msg $ "boolean length should be 1, got: " <+> show other
  map (/= 0) p_get

export
parse_integer : (Cons (Posed Bits8) i, Monoid i) => Parser i (SimpleError String) Integer
parse_integer = do
  n <- parse_tl 0x02
  bits <- count n p_get
  case fromList $ toList bits of
    Just x => pure $ signed_be_to_integer x
    Nothing => fail $ msg "integer length is 0"

export
parse_bitstring : (Cons (Posed Bits8) i, Monoid i) => Parser i (SimpleError String) Bitstring
parse_bitstring = do
  (S n) <- parse_tl 0x03
  | Z => fail $ msg "bitstring length is 0"
  pad_len <- p_get
  bits <- toList <$> count n p_get
  pure $ MkBitstring (cast pad_len) bits

export
parse_octet_string : (Cons (Posed Bits8) i, Monoid i) => Parser i (SimpleError String) (List Bits8)
parse_octet_string = do
  n <- parse_tl 0x04
  map toList (count n p_get)

export
parse_null : (Cons (Posed Bits8) i, Monoid i) => Parser i (SimpleError String) ()
parse_null = do
  0 <- parse_tl 0x05
  | other => fail $ msg $ "null length should be 0, got: " <+> show other
  pure ()

export
parse_oid : (Cons (Posed Bits8) i, Monoid i) => Parser i (SimpleError String) (List Integer)
parse_oid = do
  (S n) <- parse_tl 0x06
  | Z => fail $ msg "oid length is 0"
  first_node <- p_get
  nodes <- toList <$> count n p_get
  pure $ decode_oid_nodes first_node nodes
