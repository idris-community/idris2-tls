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

process_key : (0 algo : Type) -> Hash algo => List Bits8 -> List Bits8
process_key algo key =
  if length key > block_nbyte {algo}
    then toList $ hash algo key
    else key <+> (List.replicate (minus (block_nbyte {algo}) $ length key) 0)

||| calculate an hmac given a key and a message
public export
hmac : (0 algo : Type) -> Hash algo => (key : List Bits8) -> (message : List Bits8) -> Vect (digest_nbyte {algo}) Bits8
hmac algo key message =
  let key = process_key algo key
      o_key_pad = zipWith xor key $ replicate (block_nbyte {algo}) 0x5c
      i_key_pad = zipWith xor key $ replicate (block_nbyte {algo}) 0x36
  in hash algo $ o_key_pad <+> (toList $ hash algo (i_key_pad <+> message))
