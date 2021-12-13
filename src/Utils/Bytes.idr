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

public export
to_be : (FiniteBits a, Cast a Bits8) => {n : _} -> {auto 0 prf : (bitSize {a}) = n * 8} -> a -> Vect n Bits8
to_be x = replace_vect (finToNatLastIsBound) (okay last)
  where
  okay : (p : Fin (S n)) -> Vect (finToNat p) Bits8
  okay FZ = []
  okay (FS wit) =
    replace_vect (cong S finToNatWeakenNeutral)
    $ ( cast {to = Bits8} (shiftR x (bitsToIndex $ Element (finToNat wit * 8) (replace {p = LT (finToNat wit * 8)} (sym prf) $ lte_plus_left 7 $ multLteMonotoneLeft (S (finToNat wit)) n 8 $ elemSmallerThanBound wit)))
      :: okay (weaken wit)
      )

public export
to_le : (FiniteBits a, Cast a Bits8) => {n : _} -> {auto 0 prf : (bitSize {a}) = n * 8} -> a -> Vect n Bits8
to_le = reverse . to_be

public export
from_be : (FiniteBits a, Cast Bits8 a) => {n : _} -> {auto 0 prf : (bitSize {a} = n * 8)} -> Vect n Bits8 -> a
from_be p = okay last (replace_vect (sym finToNatLastIsBound) p)
  where
  okay : (x : Fin (S n)) -> Vect (finToNat x) Bits8 -> a
  okay FZ [] = zeroBits
  okay (FS wit) (z :: zs) = ( shiftL (cast {to = a} z) (bitsToIndex $ Element (finToNat wit * 8) (replace {p = LT (finToNat wit * 8)} (sym prf) $ lte_plus_left 7 $ multLteMonotoneLeft (S (finToNat wit)) n 8 $ elemSmallerThanBound wit)) ) .|. okay (weaken wit) (replace_vect (sym finToNatWeakenNeutral) zs)

public export
from_le : (FiniteBits a, Cast Bits8 a) => {n : _} -> {auto 0 prf : (bitSize {a} = n * 8)} -> Vect n Bits8 -> a
from_le = from_be . reverse

public export
set_bit_to : Bits a => Bool -> Index {a} -> a -> a
set_bit_to False _ x = x
set_bit_to True pos x = setBit x pos

public export
rotate_right'' : FiniteBits a => {auto prf : LTE 2 (bitSize {a})} -> Bool -> a -> a
rotate_right'' carry x =
  case @@ bitSize {a = a} of
    (Z ** okay) => absurd $ replace {p = LTE 2} okay prf
    (S bit_size ** okay) =>
      set_bit_to carry (bitsToIndex $ Element bit_size (replace {p = LTE (S bit_size)} (sym okay) (reflexive {x = S bit_size}))) $ shiftR x (bitsToIndex $ Element 1 prf)

public export
rotate_right' : FiniteBits a => {auto prf : LTE 2 (bitSize {a})} -> a -> a
rotate_right' x = rotate_right'' {prf} (testBit x (bitsToIndex $ Element 0 (lteSuccLeft prf))) x

public export
rotate_right : FiniteBits a => {auto prf : LTE 2 (bitSize {a})} -> Nat -> a -> a
rotate_right Z x = x
rotate_right (S n) x = rotate_right {prf} n (rotate_right' {prf} x)

public export
to_bools_be' : FiniteBits a => (n : Fin (S (bitSize {a}))) -> a -> Vect (finToNat n) Bool
to_bools_be' FZ x = []
to_bools_be' (FS wit) x = testBit x (bitsToIndex $ Element (finToNat wit) (elemSmallerThanBound wit)) :: (replace_vect finToNatWeakenNeutral $ to_bools_be' (weaken wit) x)

public export
to_bools_be : FiniteBits a => a -> Vect (bitSize {a}) Bool
to_bools_be x = replace_vect finToNatLastIsBound $ to_bools_be' {a = a} Fin.last x

public export
le_to_integer : {n : Nat} -> Vect n Bits8 -> Integer
le_to_integer v = foldr (.|.) 0 $ zipWith shiftL (cast {to=Integer} <$> v) (((*8) . finToNat) <$> Fin.range)

public export
le_to_integer' : List Bits8 -> Integer
le_to_integer' v =
  foldr (.|.) 0 $ zipWith shiftL (cast {to=Integer} <$> v) ((*8) <$> [0..(length v)])

public export
be_to_integer : {n : Nat} -> Vect n Bits8 -> Integer
be_to_integer = le_to_integer . reverse

public export
be_to_integer' : List Bits8 -> Integer
be_to_integer' = le_to_integer' . reverse 

public export
integer_to_le : (n : Nat) -> Integer -> Vect n Bits8
integer_to_le n v = (cast . shiftR v) <$> (((*8) . finToNat) <$> Fin.range)

public export
integer_to_be : (n : Nat) -> Integer -> Vect n Bits8
integer_to_be n = reverse . integer_to_le n

public export
to_digit : Bool -> Char
to_digit False = '0'
to_digit True = '1'

public export
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
xxd : List Bits8 -> String
xxd = concat . intersperse " " . map show_hex

public export
string_to_ascii : (x : String) -> List Bits8
string_to_ascii = map (cast . ord) . unpack

public export
ascii_to_string : List Bits8 -> String
ascii_to_string = pack . map cast
