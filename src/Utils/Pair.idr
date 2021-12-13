module Utils.Pair

infixl 0 :>

||| A pair with its second argument being lazy, heavily using in `Extra.Streaming`
public export
data Of : (a : Type) -> (b : Type) -> Type where
  (:>) : a -> Lazy b -> Of a b

export
Bifunctor Of where
  mapFst f (a :> b) = f a :> b
  mapSnd f (a :> b) = a :> f b
  bimap f g (a :> b) = f a :> g b

export
Functor (Of a) where
  map = mapSnd
