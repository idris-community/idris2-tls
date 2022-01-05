module Crypto.Hash.Interfaces

import Data.Vect

public export
interface Digest (0 algo : Type) where
  digest_nbyte : Nat
  update : List Bits8 -> algo -> algo
  finalize : algo -> Vect digest_nbyte Bits8

public export
interface Digest algo => Hash algo where
  block_nbyte : Nat
  initialize : algo

public export
interface Digest algo => MAC (0 key : Type) algo where
  initialize_mac : key -> algo
