module Utils.Parser

import Debug.Trace
import Data.List
import Data.List.Elem
import Data.List1
import Data.Vect
import Data.Void
import Decidable.Equality
import Syntax.WithProof

public export
interface Cons a s | s where
  singleton : a -> s
  uncons : s -> Maybe (a, s)

public export
Cons Char String where
  singleton = cast
  uncons = strUncons

public export
Cons a (List a) where
  singleton = pure
  uncons [] = Nothing
  uncons (x :: xs) = Just (x, xs)

||| a simple incremental parser
public export
data Parser : (input : Type) -> (error : Type) -> (a : Type) -> Type where
  Fail : e -> Parser i e a
  Pure : (leftover : i) -> a -> Parser i e a
  More : (on_feed : (i -> Parser i e a)) -> Parser i e a
  Alt : Parser i e a -> Lazy (Parser i e a) -> Parser i e a

public export
Functor (Parser i e) where
  map f (Fail e) = Fail e
  map f (Pure leftover x) = Pure leftover (f x)
  map f (More on_feed) = More (map f . on_feed)
  map f (Alt p1 p2) = Alt (map f p1) (map f p2)

||| maps over the errors of the parser
public export
map_error : (e -> e') -> Parser i e a -> Parser i e' a
map_error f (Fail e) = Fail (f e)
map_error f (Pure leftover x) = Pure leftover x
map_error f (More on_feed) = More (map_error f . on_feed)
map_error f (Alt p1 p2) = Alt (map_error f p1) (map_error f p2)

public export
(<|>) : Semigroup e => Parser i e a -> Lazy (Parser i e a) -> Parser i e a
Fail e <|> p = map_error (e <+>) p
Pure leftover x <|> p = Pure leftover x
p <|> q = Alt p q

||| fail with an error
public export
fail : e -> Parser i e a
fail = Fail

||| feed input into the parser incrementally
public export
feed : (Semigroup e, Semigroup i) => i -> Parser i e a -> Parser i e a
feed input (Fail e) = Fail e
feed input (Pure leftover x) = Pure (leftover <+> input) x
feed input (More on_feed) = on_feed input
feed input (Alt p1 p2) = feed input p1 <|> feed input p2

apply : (Semigroup e, Semigroup i) => (Parser i e a -> Parser i e b) -> Parser i e a -> Parser i e b
apply f (Fail msg) = Fail msg
apply f (Alt p1 p2) = Alt (f p1) (f p2)
apply f (More on_feed) = More (f . on_feed)
apply f parser = More (\input => f $ feed input parser)

public export
pure : Monoid i => a -> Parser i e a
pure x = Pure neutral x

public export
(<*>) : (Semigroup e, Monoid i) => Parser i e (a -> b) -> Lazy (Parser i e a) -> Parser i e b
Pure leftover f <*> p = map f $ feed leftover p
p1 <*> p2 = apply (<*> p2) p1

public export
(<*) : (Semigroup e, Monoid i) => Parser i e a -> Parser i e b -> Parser i e a
x <* y = map const x <*> y

public export
(*>) : (Semigroup e, Monoid i) => Parser i e a -> Parser i e b -> Parser i e b
x *> y = map (const id) x <*> y

public export
(>>=) : (Semigroup e, Monoid i) => Parser i e a -> (a -> Parser i e b) -> Parser i e b
(>>=) (Pure leftover x) f = feed leftover $ f x
(>>=) p f = apply (>>= f) p

public export
more : (i -> Parser i e a) -> Parser i e a
more = More

||| peek into the next token without consuming it
public export
peek : Cons c i => Parser i e c
peek = more $ \input =>
  case uncons input of
    Just (x, _) => Pure input x
    Nothing => peek

||| reads the next token
public export
token : Cons c i => Parser i e c
token = more $ \input =>
  case uncons input of
    Just (x, xs) => Pure xs x
    Nothing => token

||| run `p` `k` times and collect the results
public export
count : (Semigroup e, Monoid i, Cons c i) => (k : Nat) -> (p : Parser i e a) -> Parser i e (Vect k a)
count Z parser = pure []
count (S k) parser = pure $ !parser :: !(count k parser)

||| return the result of `p` if it succeeds, otherwise return `x`
public export
option : (Semigroup e, Monoid i) => (x : a) -> (p : Parser i e a) -> Parser i e a
option x p = p <|> pure x

mutual
  public export
  some : (Semigroup e, Monoid i) => Parser i e a -> Parser i e (List1 a)
  some p = pure $ !p ::: !(many p)

  public export
  many : (Semigroup e, Monoid i) => Parser i e a -> Parser i e (List a)
  many p = option [] (forget <$> some p)

namespace Error
  ||| example: `SimpleError String`
  public export
  data SimpleError : Type -> Type where
    Msg : a -> SimpleError a
    Alt : SimpleError a -> SimpleError a -> SimpleError a
    Under : a -> SimpleError a -> SimpleError a

  public export
  Semigroup (SimpleError a) where
    (<+>) = Alt

  public export
  Show a => Show (SimpleError a) where
    show (Msg x) = show x
    show (Alt a b) = "(" <+> show a <+> " <|> " <+> show b <+> ")"
    show (Under x a) = "(" <+> show x <+> ": " <+> show a <+> ")"

  public export
  msg : e -> SimpleError e
  msg = Msg

  public export
  under : e -> Parser i (SimpleError e) a -> Parser i (SimpleError e) a
  under = map_error . Under
