module Utils.Base64

import Control.Monad.Trans
import Data.Bits
import Data.List
import Data.String.Parser
import Data.Vect
import Debug.Trace
import Utils.Bytes
import public Control.Monad.Identity

alphabets : List Char
alphabets = unpack "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

padding : Char
padding = '='

index_to_alphabet : List (Integer, Char)
index_to_alphabet = zip [0..64] alphabets

alphabet_to_index : List (Char, Integer)
alphabet_to_index = zip alphabets [0..64]

export
is_base64_char : Char -> Bool
is_base64_char c = isAlphaNum c || (c == '+') || (c == '/') || (c == '=')

base64_char : Monad m => ParseT m Integer
base64_char = do
  c <- satisfy $ const True
  case lookup c alphabet_to_index of
    Just i => pure i
    Nothing => fail "expected base64 character"

parse_base64 : Monad m => ParseT m (List Bits8)
parse_base64 = do
  alphas <- many base64_char
  paddings <- many (char padding)
  eos
  let unpadded     = foldr (.|.) 0 $ zipWith shiftL (reverse alphas) ((*6) <$> [0..(length alphas)])
  let padded       = shiftR unpadded (2 * (length paddings))
  let bytes_length = (minus (6 * length alphas) (2 * length paddings)) `div` 8
  pure $ reverse $ toList $ integer_to_le bytes_length padded

export
base64_decode : String -> Either String (List Bits8)
base64_decode x = fst <$> parse parse_base64 x
