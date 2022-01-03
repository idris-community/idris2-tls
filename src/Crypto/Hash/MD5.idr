module Crypto.Hash.MD5

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
data MD5 : Type where
  MkMD5 : MerkleDamgard 4 64 Bits32 -> MD5

k_table : Vect 64 Bits32
k_table =
  [ 0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee
  , 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501
  , 0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be
  , 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821
  , 0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa
  , 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8
  , 0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed
  , 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a
  , 0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c
  , 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70
  , 0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05
  , 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665
  , 0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039
  , 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1
  , 0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1
  , 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391 ]

s_table : Vect 64 (Fin 32)
s_table =
  [ 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22
  , 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20
  , 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23
  , 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21 ]

i_table : Vect 64 (Fin 16)
i_table =
  [ 0, 1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15
  , 1, 6, 11,  0,  5, 10, 15,  4,  9, 14,  3,  8, 13,  2,  7, 12
  , 5, 8, 11, 14,  1,  4,  7, 10, 13,  0,  3,  6,  9, 12, 15,  2
  , 0, 7, 14,  5, 12,  3, 10,  1,  8, 15,  6, 13,  4, 11,  2,  9 ]

s_k_table : Vect 64 (Fin 32, Bits32)
s_k_table = zip s_table k_table

md5_init_hash_values : Vect 4 Bits32
md5_init_hash_values = [ 0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476 ]

md5_compress : (block : Vect 64 Bits8) -> (h : Vect 4 Bits32) -> Vect 4 Bits32
md5_compress block hash_values = zipWith (+) hash_values $ go (_ ** zip calc_m_g s_k_table) hash_values
  where
  calc_m_g : Vect 64 Bits32
  calc_m_g =
    let block' = map (from_le {a = Bits32} {n = 4}) $ group 16 4 block
    in map (\i => index i block') i_table
  loop : Bits32 -> Bits32 -> Bits32 -> Fin 32 -> Bits32 -> Bits32 -> Bits32 -> Bits32 -> Vect 4 Bits32
  loop f m_g k_i s_i a b c d =
    let f = f + a + k_i + m_g
        a = d
        d = c
        c = b
        b = b + rotl s_i f
    in [a, b, c, d]
  go : (n ** Vect n (Bits32, Fin 32, Bits32)) -> Vect 4 Bits32 -> Vect 4 Bits32
  go (Z ** []) abcd = abcd
  go ((S n) ** ((i, s_i, k_i) :: xs)) [a, b, c, d] =
    case n `div` 16 of
      3 => go (n ** xs) $ loop (d `xor` (b .&. (c `xor` d)))    i k_i s_i a b c d
      2 => go (n ** xs) $ loop (c `xor` (d .&. (b `xor` c)))    i k_i s_i a b c d
      1 => go (n ** xs) $ loop (b `xor` c `xor` d)              i k_i s_i a b c d
      _ => go (n ** xs) $ loop (c `xor` (b .|. (complement d))) i k_i s_i a b c d

md5_update : List Bits8 -> MD5 -> MD5
md5_update input (MkMD5 s) =
  let
    Fraction _ 64 nblocks residue_nbyte prf = divMod (s.buffer_nbyte + length input) 64
    (blocks, residue) = splitAt (mult nblocks 64) (replace_vect (sym prf) (s.buffer ++ fromList input))
  in
    MkMD5 $ {buffer := residue, buffer_nbyte := _, buffer_nbyte_constraint := elemSmallerThanBound residue_nbyte }
      ( foldl (\s_, block_ => {hash_values $= md5_compress block_, npassed_blocks $= S} s_) s (group nblocks 64 blocks) )

md5_finalize : MD5 -> Vect 16 Bits8
md5_finalize (MkMD5 s) =
  concat $ map (to_le {n = 4}) $
    case pad_theorem {block_nbyte = 64} {residue_max_nbyte = 55} {length_nbyte = 8} (LTESucc LTEZero) Refl s.buffer_nbyte_constraint s.buffer (integer_to_le _ $ 8 * (cast s.npassed_blocks * 64 + cast s.buffer_nbyte)) of
      Left block => md5_compress block s.hash_values
      Right blocks => let (x1, x2) = splitAt 64 blocks in md5_compress x2 $ md5_compress x1 s.hash_values

export
Hash MD5 where
  block_nbyte = 64
  digest_nbyte = 16
  initialize = MkMD5 $ mk_merkle_damgard md5_init_hash_values
  update = md5_update
  finalize = md5_finalize
