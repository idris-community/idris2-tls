module Utils.ConstantTable

import Data.Vect
import Data.Fin
import Data.IOArray.Prims
import PrimIO

||| A constant table that can be read in O(1) time
export
data ConstantTable : Nat -> Type -> Type where
  MkFromArray : ArrayData e -> ConstantTable (S n) e

export
length : {n : Nat} -> ConstantTable n e -> Nat
length _ = n

export
index : Fin (S n) -> ConstantTable (S n) a -> a
index n (MkFromArray array) = unsafePerformIO $ primIO $ prim__arrayGet array (cast $ finToInteger n)

export
index_bits8 : Bits8 -> ConstantTable 256 a -> a
index_bits8 n (MkFromArray array) = unsafePerformIO $ primIO $ prim__arrayGet array (cast n)

export
from_vect : {n : Nat} -> Vect (S n) a -> ConstantTable (S n) a
from_vect (x :: xs) = unsafePerformIO $ do
  array <- primIO $ prim__newArray (cast (S n)) x
  let indexed_array = zip (drop 1 Fin.range) xs
  traverse_ (\(i,v) => primIO $ prim__arraySet array (cast $ finToInteger i) v) indexed_array
  pure $ MkFromArray array
