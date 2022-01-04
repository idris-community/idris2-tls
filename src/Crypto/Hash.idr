module Crypto.Hash

import Data.Bits
import Data.List
import Data.Nat
import Data.Vect
import public Crypto.Hash.Interfaces
import public Crypto.Hash.SHA2
import public Crypto.Hash.SHA1
import public Crypto.Hash.MD5

||| basically `Hash.initialize` but with explicit type argument
public export
init : (0 algo : Type) -> Hash algo => algo
init algo = initialize

||| hash a sequence of bytes and produce a digest
public export
hash : (0 algo : Type) -> Hash algo => (message : List Bits8) -> Vect (digest_nbyte {algo}) Bits8
hash algo xs = finalize $ update xs $ Hash.init algo

||| basically `MAC.initialize` but with explicit type argument
public export
init_mac : (0 algo : Type) -> MAC key algo => key -> algo
init_mac algo key = initialize_mac key

||| hash a sequence of bytes with key and produce a digest
public export
mac : (0 algo : Type) -> MAC key algo => key -> (message : List Bits8) -> Vect (digest_nbyte {algo}) Bits8
mac algo key xs = finalize $ update xs $ Hash.init_mac algo key
