module Crypto.Hash.Interfaces

import Data.Vect

public export
interface Hash (0 algo : Type) where
  digest_nbyte : Nat
  block_nbyte : Nat
  initialize : algo
  update : List Bits8 -> algo -> algo
  finalize : algo -> Vect digest_nbyte Bits8
