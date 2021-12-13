module Network.TLS.Parsing

import Data.List1
import Data.Vect
import Utils.Bytes
import public Utils.Parser

namespace Parserializer
  ||| bidirectional serializer
  ||| `decode` is assumed to be the inverse of `encode` and vice versa
  public export
  record Parserializer (c : Type) (i : Type) (e : Type) (a : Type) where
    constructor MkParserializer
    encode : a -> List c
    decode : Parser i e a

  infixr 5 <*>>

  export
  apair : (Semigroup e, Monoid i) => Parserializer c i e a -> Parserializer c i e b -> Parserializer c i e (a, b)
  apair ma mb = MkParserializer (\(a, b) => ma.encode a <+> mb.encode b) $ (,) <$> ma.decode <*> mb.decode

  ||| infixr for `apair`
  export
  (<*>>) : (Semigroup e, Monoid i) => Parserializer c i e a -> Parserializer c i e b -> Parserializer c i e (a, b)
  (<*>>) = apair

  export
  map : (to : a -> b) -> (from : b -> a) -> Parserializer c i e a -> Parserializer c i e b
  map to from pser = MkParserializer (pser.encode . from) (map to pser.decode)

  export
  (*>) : (Semigroup e, Monoid i) => Parserializer c i e () -> Parserializer c i e a -> Parserializer c i e a
  ma *> mb = map snd ((),) (ma <*>> mb)

  export
  (<*) : (Semigroup e, Monoid i) => Parserializer c i e a -> Parserializer c i e () -> Parserializer c i e a
  ma <* mb = map fst (,()) (ma <*>> mb)

  export
  aeither : (Semigroup e, Monoid i) => Parserializer c i e a -> Parserializer c i e b -> Parserializer c i e (Either a b)
  aeither ma mb = MkParserializer (either ma.encode mb.encode) $ (map Left ma.decode) <|> (map Right mb.decode)

  export
  (<|>) : (Semigroup e, Monoid i) => Parserializer c i e a -> Parserializer c i e b -> Parserializer c i e (Either a b)
  (<|>) = aeither

||| primarily used for `hack_*` functions for hacking open ADTs into sums ^/v products
public export
Eithers : List Type -> Type
Eithers [] = Void
Eithers (x :: []) = x
Eithers (x :: xs) = Either x (Eithers xs)

||| essentially (Nat, `a`), where Nat denotes the position, usually starts with 0
public export
record Posed (a : Type) where
  constructor MkPosed
  pos : Nat
  get : a

||| `Parser.token` but for `Posed`
export
p_get : Cons (Posed c) i => Parser i e c
p_get = map get token

-- serializer utils

||| prepend the length of `body` into `n` bytes in big endian
export
prepend_length : (n : Nat) -> (body : List Bits8) -> List Bits8
prepend_length n body = (toList $ integer_to_be n $ cast $ length body) <+> body

-- parser utils

||| parse the next `n` bytes as a natural number in big endian style
export
p_nat : (Semigroup e, Monoid i, Cons (Posed Bits8) i) => (n : Nat) -> Parser i e Nat
p_nat n = cast {to = Nat} . be_to_integer <$> count n p_get

||| make sure that `p` MUST consume at least `n` tokens, fails otherwise
public export
p_exact : (Cons c i, Monoid i) => (n : Nat) -> (p : Parser i (SimpleError String) a) -> Parser i (SimpleError String) a
p_exact Z (Pure leftover x) = pure x
p_exact (S i) (Pure leftover x) = fail $ msg $ "over fed, " <+> show (S i) <+> " bytes more to go"
p_exact i (Fail msg) = fail msg
p_exact Z parser = fail $ msg $ "under fed, wants more"
p_exact (S i) parser = do
  b <- token
  p_exact i (feed (singleton b) parser)

--- parserializer utils

||| put parser error messages under another message
||| used for creating a treeish error message
export
under : e -> Parserializer c i (SimpleError e) a -> Parserializer c i (SimpleError e) a
under msg pser = MkParserializer pser.encode (under msg pser.decode)

||| parserialize a single posed token
export
token : (Semigroup e, Cons (Posed c) i, Monoid i) => Parserializer c i e c
token = MkParserializer pure p_get

||| parserialize `n` posed tokens
export
ntokens : (Semigroup e, Cons (Posed c) i, Monoid i) => (n : Nat) -> Parserializer c i e (Vect n c)
ntokens n = MkParserializer (toList) (count n p_get)

||| parserialize the next `n` bytes in big endian style as a length describing the number of bytes of the following data to be fed to `pser`
export
lengthed : (Cons (Posed Bits8) i, Monoid i) => (n : Nat) -> (pser : Parserializer Bits8 i (SimpleError String) a) -> Parserializer Bits8 i (SimpleError String) a
lengthed n pser = MkParserializer (prepend_length n . pser.encode) $ do
  len <- p_nat n
  p_exact len pser.decode

||| parserialize the next `n` bytes in big endian style as a length describing the number of bytes of the following data to be fed to `pser`
||| when `pser` completes, the result becomes an entry in the resulting list
||| when there are exactly zero bytes left, the list of results is returned
||| if under feeding `pser` for the last entry, the parser fails
export
lengthed_list : (Cons (Posed Bits8) i, Monoid i) => (n : Nat) -> (pser : Parserializer Bits8 i (SimpleError String) a) -> Parserializer Bits8 i (SimpleError String) (List a)
lengthed_list youmu pser = MkParserializer (prepend_length youmu . concat . map pser.encode) $ do
  S len <- p_nat youmu
  | Z => pure []
  go (S len) pser.decode
  where
  go : Nat -> Parser i (SimpleError String) a -> Parser i (SimpleError String) (List a)
  go Z (Pure leftover x) = pure [x]
  go (S i) (Pure leftover x) = (x ::) <$> go (S i) pser.decode
  go i (Fail msg) = fail msg
  go Z parser = fail $ msg $ "under fed, want more"
  go (S i) parser = do
    b <- token
    go i (feed (singleton b) parser)

||| `lengthed_list` but `List1`
export
lengthed_list1 : (Cons (Posed Bits8) i, Monoid i) => (youmu : Nat) -> Parserializer Bits8 i (SimpleError String) a -> Parserializer Bits8 i (SimpleError String) (List1 a)
lengthed_list1 youmu pser =
  let
    pser' = lengthed_list youmu pser
  in
    MkParserializer (pser'.encode . toList) $ do
      (x :: xs) <- pser'.decode
      | [] => fail $ msg $ "empty list"
      pure (x ::: xs)

||| basically the parserializer version of `p_nat`
export
nat : Semigroup e => (Cons (Posed Bits8) i, Monoid i) => (n : Nat) -> Parserializer Bits8 i e Nat
nat n = MkParserializer (toList . integer_to_be n . cast) (p_nat n)

||| parserialize a list of bytes with nice error messages specialized for displaying byte sequences
export
is : (Cons (Posed Bits8) i, Monoid i) => {k : Nat} -> Vect (S k) Bits8 -> Parserializer Bits8 i (SimpleError String) ()
is cs = MkParserializer (const $ toList cs) $ do
  bs <- count (S k) token
  let cs' = map get bs
  case cs == cs' of
    True => pure ()
    False => 
      let
        (begin, end) = mapHom pos (head bs, last bs)
      in
        fail $ msg $ "at position " <+> show begin <+> "-" <+> show end <+> ", expected " <+> xxd (toList cs) <+> " but got " <+> xxd (toList cs')
