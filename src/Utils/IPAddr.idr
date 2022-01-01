module Utils.IPAddr

import Data.String.Parser
import Data.Vect
import Data.Fin
import Data.String.Extra
import Data.String
import Utils.Num
import Utils.Misc
import Data.List
import Data.List1
import Data.Bits
import Utils.Bytes

public export
record IPv4Addr where
  constructor MkIPv4Addr
  body : Vect 4 (Fin 256)

public export
Show IPv4Addr where
  show x = join "." $ map show x.body

public export
Eq IPv4Addr where
  x == y = x.body == y.body

public export
record IPv6Addr where
  constructor MkIPv6Addr
  body : Vect 16 (Fin 256)

bits16_show : Bits16 -> String
bits16_show x = (show_hex (cast $ shiftR x 8)) <+> (show_hex $ cast x)

to_bits16 : Vect 2 (Fin 256) -> Bits16
to_bits16 a = from_be $ map (cast {to=Bits8} . finToInteger) a

to_hextets : IPv6Addr -> Vect 8 Bits16
to_hextets addr = map to_bits16 $ group 8 2 addr.body

public export
Show IPv6Addr where
  show x = assert_total $ join ":" $ map bits16_show (to_hextets x)

public export
Eq IPv6Addr where
  x == y = x.body == y.body

read_decimal_byte : Monad m => ParseT m (Fin 256)
read_decimal_byte = do
  n <- natural
  case natToFin n 256 of
    Just x => pure x
    Nothing => fail "number out of bound"

parse_ipv4' : Monad m => ParseT m IPv4Addr
parse_ipv4' = do
  a <- read_decimal_byte
  _ <- char '.'
  b <- read_decimal_byte
  _ <- char '.'
  c <- read_decimal_byte
  _ <- char '.'
  d <- read_decimal_byte
  pure $ MkIPv4Addr [a, b, c, d]

export
parse_ipv4 : String -> Either String IPv4Addr
parse_ipv4 = map fst . parse parse_ipv4'

data IPv6R : Type -> Type where
  One : a -> IPv6R a
  Two : a -> a -> IPv6R a

splitDoubleColon : String -> Either String (IPv6R String)
splitDoubleColon str = do
  let (a ::: [b]) = split ((':', ':') ==) (f $ unpack str)
  | (a ::: []) => pure (One str)
  | _ => Left "too many double colons"
  pure $ Two (pack $ map fst a) (pack $ map snd b)
  where
    f : List Char -> List (Char, Char)
    f [] = []
    f (x :: xs) = zip (x :: xs) xs

parse_ipv6_to_octets : String -> Either String (IPv6R (List Bits16))
parse_ipv6_to_octets string = do
  Two a b <- splitDoubleColon string
  | One a => One <$> to a
  a <- to a
  b <- to b
  pure $ Two a b
  where
    go : String -> Either String Bits16
    go x = do
      let Just hex = stringToNat' 16 x
      | Nothing => Left $ "invalid hextet: " <+> x
      if hex < 65536
        then Right $ cast hex
        else Left "number out of bound"
    to : String -> Either String (List Bits16)
    to "" = Right []
    to x = traverse go $ toList $ split (':' ==) x

parse_ipv6_expand_columns : IPv6R (List Bits16) -> Either String (Vect 8 Bits16)
parse_ipv6_expand_columns (One a) = maybe_to_either (exactLength _ $ fromList a) "invalid length"
parse_ipv6_expand_columns (Two a b) = do
  let plen = minus 8 (length a + length b)
  let apb = a <+> replicate plen 0 <+> b
  maybe_to_either (exactLength _ $ fromList apb) "invalid length"

explode_bits16 : Bits16 -> Vect 2 (Fin 256)
explode_bits16 x =
  let a = modFinNZ (cast (shiftR x 8)) 256 SIsNonZero
      b = modFinNZ (cast x) 256 SIsNonZero
  in [a, b]

export
parse_ipv6 : String -> Either String IPv6Addr
parse_ipv6 x = do
  y <- (parse_ipv6_to_octets x >>= parse_ipv6_expand_columns)
  pure $ MkIPv6Addr $ concat $ map explode_bits16 y
