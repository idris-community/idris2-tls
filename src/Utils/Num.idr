module Utils.Num

import Data.Vect

alphabets : Vect 36 Char
alphabets = fromList $ unpack "0123456789abcdefghijklmnopqrstuvwxyz"

-- Use integer for performance reason
export
stringToNat' : Fin 36 -> String -> Maybe Integer
stringToNat' base str = if str == "" then Nothing else go (finToInteger base) 1 0 $ reverse $ unpack str
  where
    go : Integer -> Integer -> Integer -> List Char -> Maybe Integer
    go base' yoyo acc [] = Just acc
    go base' yoyo acc (chr :: xs) = do
      i <- elemIndex chr alphabets
      if i < base then go base' (base' * yoyo) (acc + finToInteger i * yoyo) xs else Nothing

export
stringToNat : Fin 36 -> String -> Maybe Nat
stringToNat base string = integerToNat <$> stringToNat' base string

export
stringToInteger : Fin 36 -> String -> Maybe Integer
stringToInteger base str =
  case strUncons str of
    Just ('-', num) => negate <$> stringToNat' base num
    Just ('+', num) => stringToNat' base num
    _ => stringToNat' base str
