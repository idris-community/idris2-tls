module Crypto.Hash.SHA1

import Crypto.Hash.Interfaces
import Data.Bits
import Data.DPair
import Data.Fin
import Data.Fin.Extra
import Data.List
import Data.Nat
import Data.Nat.Factor
import Data.Vect
import Utils.Misc
import Utils.Bytes
import Data.Stream
import Crypto.Hash.MerkleDamgard

export
data Sha1 : Type where
  MkSha1 : MerkleDamgard 5 64 Bits32 -> Sha1

sha1_init_hash_values : Vect 5 Bits32
sha1_init_hash_values =
  [ 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0 ]

sha1_extend_message : Vect 16 Bits32 -> Stream Bits32
sha1_extend_message xs = prepend (toList xs) $ go xs
  where
  go : Vect 16 Bits32 -> Stream Bits32
  go xs =
    let
      [wi_16, wi_14, wi_8, wi_3] = the (Vect 4 _) $ map (flip index xs) [0, 2, 8, 13]
      w = rotl 1 (wi_16 `xor` wi_14 `xor` wi_8 `xor` wi_3)
    in
      w :: go (tail xs `snoc` w)

sha1_compress : (block : Vect 64 Bits8) -> (h : Vect 5 Bits32) -> Vect 5 Bits32
sha1_compress block hash_values = zipWith (+) hash_values $ go Z (sha1_extend_message $ map (from_be {a = Bits32} {n = 4}) $ group 16 4 block) hash_values
  where
  loop : Bits32 -> Bits32 -> Bits32 -> Bits32 -> Bits32 -> Bits32 -> Bits32 -> Bits32 -> Vect 5 Bits32
  loop f k wi a b c d e =
    let temp = (rotl 5 a) + f + e + k + wi
        e = d
        d = c
        c = rotl 30 b
        b = a
        a = temp
    in [a, b, c, d, e]
  go :  Nat -> Stream Bits32 -> Vect 5 Bits32 -> Vect 5 Bits32
  go n (wi :: ws) abc@[a, b, c, d, e] =
    case n `div` 20 of
      0 => go (S n) ws $ loop ((b .&. c) .|. ((complement b) .&. d))  0x5A827999 wi a b c d e
      1 => go (S n) ws $ loop (b `xor` c `xor` d)                     0x6ED9EBA1 wi a b c d e
      2 => go (S n) ws $ loop ((b .&. c) .|. (b .&. d) .|. (c .&. d)) 0x8F1BBCDC wi a b c d e
      3 => go (S n) ws $ loop (b `xor` c `xor` d)                     0xCA62C1D6 wi a b c d e
      _ => abc

sha1_update : List Bits8 -> Sha1 -> Sha1
sha1_update input (MkSha1 s) =
  let
    Fraction _ 64 nblocks residue_nbyte prf = divMod (s.buffer_nbyte + length input) 64
    (blocks, residue) = splitAt (mult nblocks 64) (replace_vect (sym prf) (s.buffer ++ fromList input))
  in
    MkSha1 $ {buffer := residue, buffer_nbyte := _, buffer_nbyte_constraint := elemSmallerThanBound residue_nbyte }
      ( foldl (\s_, block_ => {hash_values $= sha1_compress block_, npassed_blocks $= S} s_) s (group nblocks 64 blocks) )

sha1_finalize : Sha1 -> Vect 20 Bits8
sha1_finalize (MkSha1 s) =
  concat $ map (to_be {n = 4}) $
    case pad_theorem {block_nbyte = 64} {residue_max_nbyte = 55} {length_nbyte = 8} (LTESucc LTEZero) Refl s.buffer_nbyte_constraint s.buffer (integer_to_be _ $ 8 * (cast s.npassed_blocks * 64 + cast s.buffer_nbyte)) of
      Left block => sha1_compress block s.hash_values
      Right blocks => let (x1, x2) = splitAt 64 blocks in sha1_compress x2 $ sha1_compress x1 s.hash_values

export
Digest Sha1 where
  digest_nbyte = 20
  update = sha1_update
  finalize = sha1_finalize

export
Hash Sha1 where
  block_nbyte = 64
  initialize = MkSha1 $ mk_merkle_damgard sha1_init_hash_values
