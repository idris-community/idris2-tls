module Network.TLS.Parse.PEM

import Control.Monad.Trans
import Data.String
import Data.String.Extra
import Data.String.Parser
import Utils.Base64
import Utils.Bytes
import Utils.Misc

public export
record PEMBlob where
  constructor MkPEMBlob
  label : String
  content : List Bits8

public export
Show PEMBlob where
  show (MkPEMBlob label content) = label <+> ": " <+> xxd content

is_label_char : Char -> Bool
is_label_char c = (not (isControl c)) && (c /= '-')

label_char : Applicative m => ParseT m Char
label_char = satisfy is_label_char <?> "expected label character"

base64_char : Applicative m => ParseT m Char
base64_char = satisfy is_base64_char <?> "expected base64 character"

takeUntil : Monad m => (stop : String) -> ParseT m ()
takeUntil stop = do
    let StrCons s top = strM stop
      | StrNil => pure ()
    takeUntil' s top
  where
    takeUntil' : Monad m' => (s : Char) -> (top : String) -> ParseT m' ()
    takeUntil' s top = do
        init <- takeWhile (/= s)
        skip $ char s <?> "end of string reached - \{show stop} not found"
        case !(succeeds $ string top) of
             False => takeUntil' s top
             True => pure ()

export
parse_pem_blob : Parser PEMBlob
parse_pem_blob = do
  takeUntil "-----BEGIN "
  label' <- many label_char
  let label = pack label'
  _ <- string "-----"
  spaces
  content <- many ((some base64_char) <* spaces)
  _ <- string "-----END "
  _ <- string label
  _ <- string "-----"
  spaces
  case base64_decode $ pack $ concat content of
    Right str => pure $ MkPEMBlob label str
    Left  err => fail $ "failed parsing PEM content: " <+> err

fold_string : String -> String
fold_string str = pack $ foldl (<+>) [] $ map (<+> ['\n']) $ chunk 64 $ unpack str

export
encode_pem_blob : PEMBlob -> String
encode_pem_blob blob =
  "-----BEGIN " <+> blob.label <+> "-----\n"
  <+> (fold_string $ base64_encode blob.content)
  <+> "-----END " <+> blob.label <+> "-----"
