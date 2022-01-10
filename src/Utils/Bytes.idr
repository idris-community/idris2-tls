module Utils.Bytes

import Syntax.WithProof
import Data.Bits
import Data.DPair
import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.List
import Data.Vect
import Data.Nat.Factor
import Data.Nat.Order.Properties
import Utils.Misc

weakenN' : {m : Nat} -> (0 n : Nat) -> Fin m -> Fin (n + m)
weakenN' n m' = rewrite plusCommutative n m in weakenN n m'

fix_fin : (m : Nat) -> (n : Nat) -> (S m) = n -> S (S (S (S (S (S (S (S (mult m 8)))))))) = mult n 8
fix_fin m n prf = rewrite sym prf in Refl

export
to_le : (FiniteBits a, Cast a Bits8) => {n : _} -> {auto 0 no0 : NonZero n} -> {auto 0 prf : n * 8 = (bitSize {a})} -> a -> Vect n Bits8
to_le x = let (S m) = n; nmeq = Refl in map (go nmeq x) Fin.range
  where
    go : {m : Nat} -> ((S m) = n) -> a -> Fin (S m) -> Bits8
    go nmeq b i = cast $ shiftR b (bitsToIndex $ coerce prf $ coerce (fix_fin m n nmeq) $ weakenN' 7 $ i * 8)

export
to_be : (FiniteBits a, Cast a Bits8) => {n : _} -> {auto 0 no0 : NonZero n} -> {auto 0 prf : n * 8 = (bitSize {a})} -> a -> Vect n Bits8
to_be = reverse . to_le

export
from_le : (FiniteBits a, Cast Bits8 a) => {n : _} -> {auto 0 no0 : NonZero n} -> {auto 0 prf : n * 8 = (bitSize {a})} -> Vect n Bits8 -> a
from_le p = let (S m) = n; nmeq = Refl in foldl (.|.) zeroBits $ zipWith (go nmeq) p Fin.range
  where
    go : {m : Nat} -> ((S m) = n) -> Bits8 -> Fin (S m) -> a
    go nmeq b i = shiftL (cast b) (bitsToIndex $ coerce prf $ coerce (fix_fin m n nmeq) $ weakenN' 7 $ i * 8)

export
from_be : (FiniteBits a, Cast Bits8 a) => {n : _} -> {auto 0 no0 : NonZero n} -> {auto 0 prf :  n * 8 = (bitSize {a})} -> Vect n Bits8 -> a
from_be = from_le . reverse

export
set_bit_to : Bits a => Bool -> Index {a} -> a -> a
set_bit_to False _ x = x
set_bit_to True pos x = setBit x pos

export
to_bools_be' : FiniteBits a => (n : Fin (S (bitSize {a}))) -> a -> Vect (finToNat n) Bool
to_bools_be' FZ x = []
to_bools_be' (FS wit) x = testBit x (bitsToIndex $ subset_to_fin $ Element (finToNat wit) (elemSmallerThanBound wit)) :: (replace_vect finToNatWeakenNeutral $ to_bools_be' (weaken wit) x)

export
to_bools_be : FiniteBits a => a -> Vect (bitSize {a}) Bool
to_bools_be x = replace_vect finToNatLastIsBound $ to_bools_be' {a = a} Fin.last x

export
le_to_integer : Foldable t => t Bits8 -> Integer
le_to_integer = go . toList
  where
  go : List Bits8 -> Integer
  go v = foldr (.|.) 0 $ zipWith shiftL (cast {to=Integer} <$> v) ((*8) <$> [0..(length v)])

export
be_to_integer : Foldable t => t Bits8 -> Integer
be_to_integer = le_to_integer . reverse . toList

export
integer_to_le : (n : Nat) -> Integer -> Vect n Bits8
integer_to_le n v = (cast . shiftR v) <$> (((*8) . finToNat) <$> Fin.range)

export
integer_to_be : (n : Nat) -> Integer -> Vect n Bits8
integer_to_be n = reverse . integer_to_le n

export
to_digit : Bool -> Char
to_digit False = '0'
to_digit True = '1'

export
show_bin : FiniteBits a => a -> String
show_bin = pack . toList . map to_digit . to_bools_be

||| if 0-15, then return the corresponding hex char
||| otherwise returns a '?'
export
hex_lower : Bits8 -> Char
hex_lower 0 = '0'
hex_lower 1 = '1'
hex_lower 2 = '2'
hex_lower 3 = '3'
hex_lower 4 = '4'
hex_lower 5 = '5'
hex_lower 6 = '6'
hex_lower 7 = '7'
hex_lower 8 = '8'
hex_lower 9 = '9'
hex_lower 10 = 'a'
hex_lower 11 = 'b'
hex_lower 12 = 'c'
hex_lower 13 = 'd'
hex_lower 14 = 'e'
hex_lower 15 = 'f'
hex_lower _ = '?'

export
show_hex : Bits8 -> String
show_hex x = strCons (hex_lower (div x 16)) $ strCons (hex_lower (mod x 16)) $ ""

||| takes a list of bytes and show them using `show_hex` interspersed by a whitespace
export
xxd : Foldable t => t Bits8 -> String
xxd = concat . intersperse " " . map show_hex . toList

export
string_to_ascii : (x : String) -> List Bits8
string_to_ascii = map (cast . ord) . unpack

export
ascii_to_string : List Bits8 -> String
ascii_to_string = pack . map cast

maybe_a_a : Lazy a -> Maybe a -> a
maybe_a_a a Nothing  = Force a
maybe_a_a _ (Just a) = a

export
shiftL' : FiniteBits a => a -> Nat -> a
shiftL' x i = maybe_a_a zeroBits $ do
  i' <- natToFin i _
  Just $ shiftL x (bitsToIndex i')

export
shiftR' : FiniteBits a => a -> Nat -> a
shiftR' x i = maybe_a_a zeroBits $ do
  i' <- natToFin i _
  Just $ shiftR x (bitsToIndex i')

fix_fin_type : (m = (S n)) -> Fin (S n) -> Fin m
fix_fin_type prf x = rewrite prf in x

export
rotl : FiniteBits a => {n : Nat} -> {auto prf : (bitSize {a} = (S n))} -> Fin (S n) -> a -> a
rotl FZ x = x
rotl (FS i) x = (shiftL x $ bitsToIndex (fix_fin_type prf $ FS i)) .|. (shiftR x $ bitsToIndex $ invFin $ fix_fin_type prf $ weaken i)

export
rotr : FiniteBits a => {n : Nat} -> {auto prf : (bitSize {a} = (S n))} -> Fin (S n) -> a -> a
rotr FZ x = x
rotr (FS i) x = (shiftR x $ bitsToIndex (fix_fin_type prf $ FS i)) .|. (shiftL x $ bitsToIndex $ invFin $ fix_fin_type prf $ weaken i)

export
b8_to_fin : Bits8 -> Fin 256
b8_to_fin x =
  case natToFin (cast x) _ of
    Just y => y
    Nothing => assert_total $ idris_crash "b8_to_fin is not working"

