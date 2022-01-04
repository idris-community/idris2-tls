module Crypto.Hash.HMAC

import Crypto.Hash
import Data.Bits
import Data.List
import Data.Vect

export
data HMAC : Type -> Type where
  MkHMAC : (o_key_pad : List Bits8) -> algo -> HMAC algo

process_key : (0 algo : Type) -> Hash algo => List Bits8 -> List Bits8
process_key algo key =
  if length key > block_nbyte {algo}
    then toList $ hash algo key
    else key <+> (List.replicate (minus (block_nbyte {algo}) $ length key) 0)

export
Hash algo => Digest (HMAC algo) where
  digest_nbyte = digest_nbyte {algo}
  finalize (MkHMAC o_key_pad underlying) = hash algo $ o_key_pad <+> toList (finalize underlying)
  update message (MkHMAC o_key_pad underlying) = MkHMAC o_key_pad $ update message underlying

export
Hash algo => MAC (List Bits8) (HMAC algo) where
  initialize_mac key =
    let key = HMAC.process_key algo key
        o_key_pad = zipWith xor key $ replicate (block_nbyte {algo}) 0x5c
        i_key_pad = zipWith xor key $ replicate (block_nbyte {algo}) 0x36
    in MkHMAC o_key_pad (update i_key_pad initialize)
