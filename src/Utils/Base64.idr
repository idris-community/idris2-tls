module Utils.Base64

import Data.Bits
import Data.List
import Data.Vect
import Utils.Bytes
import Utils.Misc

%default total

alphabets : Vect 64 Char
alphabets = fromList $ unpack "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

padding : Char
padding = '='

export
is_base64_char : Char -> Bool
is_base64_char c = isAlphaNum c || (c == '+') || (c == '/') || (c == '=')

many_to_bits8 : List Bits8 -> Either String (List Bits8)
many_to_bits8 [] = Right []
many_to_bits8 [x] = Left "underfed, not enough base64 chars"
many_to_bits8 [a, b] = Right [ (shiftL a 2) .|. (shiftR b 4) ]
many_to_bits8 [a, b, c] = Right [ (shiftL a 2) .|. (shiftR b 4), (shiftL b 4) .|. (shiftR c 2) ]
many_to_bits8 (a :: b :: c :: d :: xs) = map (four_to_three a b c d <+>) (many_to_bits8 xs)
  where
    four_to_three : Bits8 -> Bits8 -> Bits8 -> Bits8 -> List Bits8
    four_to_three a b c d = [(shiftL a 2) .|. (shiftR b 4), (shiftL b 4) .|. (shiftR c 2), (shiftL (c .&. 0b11) 6) .|. d]

parse_base64 : List Char -> Either String (List Bits8)
parse_base64 [] = Right []
parse_base64 ['='] = Right []
parse_base64 ['=', '='] = Right []
parse_base64 (c :: cs) = case elemIndex c alphabets of
  Just i => [| pure (cast $ finToInteger i) :: parse_base64 cs |]
  Nothing => Left $ "invalid base64 character: " <+> show c


three_to_four : Bits8 -> Bits8 -> Bits8 -> List Char
three_to_four a b c =
  let i = shiftR a 2
      j = (shiftL (a .&. 0b11) 4) .|. (shiftR b 4)
      k = (shiftL (b .&. 0b1111) 2) .|. (shiftR c 6)
      l = c .&. 0b111111
      ijkl =
        [ modFinNZ (cast i) 64 SIsNonZero
        , modFinNZ (cast j) 64 SIsNonZero
        , modFinNZ (cast k) 64 SIsNonZero
        , modFinNZ (cast l) 64 SIsNonZero
        ]
  in (\x => index x alphabets) <$> ijkl

bits8_to_many : List Bits8 -> List Char
bits8_to_many [] = []
bits8_to_many [a] = (take 2 $ three_to_four a 0 0) <+> [padding, padding]
bits8_to_many [a, b] = (take 3 $ three_to_four a b 0) <+> [padding]
bits8_to_many (a :: b :: c :: xs) = three_to_four a b c <+> bits8_to_many xs

export
base64_decode : String -> Either String (List Bits8)
base64_decode = many_to_bits8 <=< parse_base64 . unpack

export
base64_encode : List Bits8 -> String
base64_encode = pack . bits8_to_many
