||| References:
||| - https://github.com/MarcelineVQ/idris2-streaming
||| - https://hackage.haskell.org/package/streaming
module Utils.Repeatedly

import Control.Monad.Trans
import Network.Socket
import System.File
import Utils.Pair

||| The `Repeatedly` type
export
data Repeatedly : (f : Type -> Type) -> (m : Type -> Type) -> (r : Type) -> Type where
  Step : Inf (f (Repeatedly f m r)) -> Repeatedly f m r
  Effect : Inf (m (Repeatedly f m r)) -> Repeatedly f m r
  Return : r -> Repeatedly f m r

export
(Functor f, Functor m) => Functor (Repeatedly f m) where
  map f (Step x) = Step (map (map f) x)
  map f (Effect x) = Effect (map (map f) x)
  map f (Return r) = Return (f r)

||| Wrap a new layer of a `Repeatedly`
export
wrap : f (Repeatedly f m r) -> Repeatedly f m r
wrap x = Step x

||| Wrap a new effect layer of a `Repeatedly`
export
effect : m (Repeatedly f m r) -> Repeatedly f m r
effect x = Effect x

||| Fold a stream
export
fold : (Functor f, Functor m) => (f a -> a) -> (m a -> a) -> (r -> a) -> Repeatedly f m r -> a
fold step effect return stream =
  case stream of
    Step x => step $ map (fold step effect return) x
    Effect x => effect $ map (fold step effect return) x
    Return r => return r

||| `fold` but different argument positions
export
build : (Functor f, Functor m) => (r -> a) -> (m a -> a) -> (f a -> a) -> Repeatedly f m r -> a
build return effect step = fold step effect return

||| Unfold a `Repeatedly`
export
unfold : (Functor f, Monad m) => (a -> m (Either r (f a))) -> a -> Repeatedly f m r
unfold f a = Effect $ do
  Right a' <- f a
    | Left r => pure (Return r)
  pure (Step (unfold f <$> a'))

mutual
  export
  (Functor f, Functor m) => Applicative (Repeatedly f m) where
    pure x = Return x
    x <*> y = do
      x' <- x
      y' <- y
      pure (x' y')

  export
  (Functor f, Functor m) => Monad (Repeatedly f m) where
    stream >>= f =
      assert_total $ case stream of
        Step x => Step (map (>>= f) x)
        Effect x => Effect (map (>>= f) x)
        Return r => f r

||| Inspect a `Repeatedly`
export
inspect : (Functor f, Monad m) => Repeatedly f m r -> m (Either r (f (Repeatedly f m r)))
inspect = fold (pure . (Right . map (effect {f} {m} . map (either pure wrap)))) join (pure . Left)

export
MonadTrans (Repeatedly f) where
  lift x = Effect (map Return x)

(HasIO m, Monad (Repeatedly f m)) => HasIO (Repeatedly f m) where
  liftIO x = lift (liftIO x)

export
to_list : Monad m => Repeatedly (Of a) m r -> m (List a, r)
to_list = fold (\(a :> b) => map (mapFst (a ::)) b) join (\x => pure (Nil, x))

export
to_list_ : Monad m => Repeatedly (Of a) m r -> m (List a)
to_list_ = fold (\(a :> b) => map (a ::) b) join (const (pure Nil))

export
from_list : Monad m => r -> List a -> Repeatedly (Of a) m r
from_list r Nil = Return r
from_list r (a :: as) = Step (a :> from_list r as)

export
from_list_ : Monad m => List a -> Repeatedly (Of a) m ()
from_list_ = from_list ()

||| Concatenate an element into a `Repeatedly`
export
cons : Monad m => a -> Repeatedly (Of a) m r -> Repeatedly (Of a) m r
cons x stream = Step (x :> stream)

||| Construct a singleton `Repeatedly`
export
yield : Monad m => a -> Repeatedly (Of a) m ()
yield x = Step (x :> Return ())

||| Transform the functor layer of a `Repeatedly`
export
mapf : (Functor f, Functor m) => (forall x. f x -> g x) -> Repeatedly f m r -> Repeatedly g m r
mapf f stream =
  case stream of
    Return r => Return r
    Effect x => Effect (map (mapf f) x)
    Step x => Step (f (map (mapf f) x))

||| Map through a `Repeatedly`
export
maps : Functor m => (a -> b) -> Repeatedly (Of a) m r -> Repeatedly (Of b) m r
maps f = mapf (mapFst f)
