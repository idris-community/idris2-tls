module Crypto.Hash.SHA2

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
import Crypto.Hash.MerkleDamgard

export
data Sha256 : Type where
  MkSha256 : MerkleDamgard 8 64 Bits32 -> Sha256

export
data Sha224 : Type where
  MkSha224 : Sha256 -> Sha224

export
data Sha512 : Type where
  MkSha512 : MerkleDamgard 8 128 Bits64 -> Sha512

export
data Sha384 : Type where
  MkSha384 : Sha512 -> Sha384

sha256_init_hash_values : Vect 8 Bits32
sha256_init_hash_values =
  [ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

sha256_round_constants : Vect 64 Bits32
sha256_round_constants =
  [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
  , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
  , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
  , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
  , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
  , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
  , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
  , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

sha256_extend_message : Vect 16 Bits32 -> Stream Bits32
sha256_extend_message xs = prepend (toList xs) $ go xs
  where
  go : Vect 16 Bits32 -> Stream Bits32
  go xs =
    let
      [wi_16, wi_15, wi_7, wi_2] = the (Vect 4 _) $ map (flip index xs) [0, 1, 9, 14]
      s0 = rotr 7  wi_15 `xor` rotr 18 wi_15 `xor` shiftR wi_15 3
      s1 = rotr 17 wi_2 ` xor` rotr 19 wi_2  `xor` shiftR wi_2  10
      w = wi_16 + s0 + wi_7 + s1
    in
      w :: go (tail xs `snoc` w)

sha256_compress : (block : Vect 64 Bits8) -> (h : Vect 8 Bits32) -> Vect 8 Bits32
sha256_compress block hash_values = zipWith (+) hash_values $ go sha256_round_constants (take _ $ sha256_extend_message $ map (from_be {a = Bits32} {n = 4}) $ group 16 4 block) hash_values
  where
  go : (ks : Vect kn Bits32) -> (ws : Vect kn Bits32) -> (h : Vect 8 Bits32) -> Vect 8 Bits32
  go [] _ h = h
  go (k :: ks) (w :: ws) [a,b,c,d,e,f,g,h] =
    let
      s1 = rotr 6 e `xor` rotr 11 e `xor` rotr 25 e
      ch = (e .&. f) `xor` (complement e .&. g)
      temp1 = h + s1 + ch + k + w
      s0 = rotr 2 a `xor` rotr 13 a `xor` rotr 22 a
      maj = (a .&. b) `xor` (a .&. c) `xor` (b .&. c)
      temp2 = s0 + maj
    in
      go ks ws [temp1 + temp2, a, b, c, d + temp1, e, f, g]

sha256_update : List Bits8 -> Sha256 -> Sha256
sha256_update input (MkSha256 s) =
  let
    Fraction _ 64 nblocks residue_nbyte prf = divMod (s.buffer_nbyte + length input) 64
    (blocks, residue) = splitAt (mult nblocks 64) (replace_vect (sym prf) (s.buffer ++ fromList input))
  in
    MkSha256 $ {buffer := residue, buffer_nbyte := _, buffer_nbyte_constraint := elemSmallerThanBound residue_nbyte }
      ( foldl (\s_, block_ => {hash_values $= sha256_compress block_, npassed_blocks $= S} s_) s (group nblocks 64 blocks) )

sha256_finalize : Sha256 -> Vect 32 Bits8
sha256_finalize (MkSha256 s) =
  concat $ map (to_be {n = 4}) $
    case pad_theorem {block_nbyte = 64} {residue_max_nbyte = 55} {length_nbyte = 8} (LTESucc LTEZero) Refl s.buffer_nbyte_constraint s.buffer (integer_to_be _ $ 8 * (cast s.npassed_blocks * 64 + cast s.buffer_nbyte)) of
      Left block => sha256_compress block s.hash_values
      Right blocks => let (x1, x2) = splitAt 64 blocks in sha256_compress x2 $ sha256_compress x1 s.hash_values

export
Hash Sha256 where
  block_nbyte = 64
  digest_nbyte = 32
  initialize = MkSha256 $ mk_merkle_damgard sha256_init_hash_values
  update = sha256_update
  finalize = sha256_finalize

sha224_init_hash_values : Vect 8 Bits32
sha224_init_hash_values =
  [ 0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4 ]

export
Hash Sha224 where
  block_nbyte = 64
  digest_nbyte = 28
  initialize = MkSha224 $ MkSha256 $ mk_merkle_damgard sha224_init_hash_values
  update xs (MkSha224 s) = MkSha224 $ update xs s
  finalize (MkSha224 s) = take _ $ finalize s

sha512_init_hash_values : Vect 8 Bits64
sha512_init_hash_values =
  [ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1
  , 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179 ]

sha512_round_constants : Vect 80 Bits64
sha512_round_constants =
  [ 0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538
  , 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242, 0x12835b0145706fbe
  , 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235
  , 0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65
  , 0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5, 0x983e5152ee66dfab
  , 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725
  , 0x06ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed
  , 0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b
  , 0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218
  , 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8, 0x19a4c116b8d2d0c8, 0x1e376c085141ab53
  , 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373
  , 0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec
  , 0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b, 0xca273eceea26619c
  , 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba, 0x0a637dc5a2c898a6
  , 0x113f9804bef90dae, 0x1b710b35131c471b, 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc
  , 0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817 ]

sha512_extend_message : Vect 16 Bits64 -> Stream Bits64
sha512_extend_message xs = prepend (toList xs) $ go xs
  where
  public export
  go : Vect 16 Bits64 -> Stream Bits64
  go xs =
    let
      [wi_16, wi_15, wi_7, wi_2] = the (Vect 4 _) $ map (flip index xs) [0, 1, 9, 14]
      s0 = rotr 1  wi_15 `xor` rotr 8  wi_15 `xor` shiftR wi_15 7
      s1 = rotr 19 wi_2  `xor` rotr 61 wi_2  `xor` shiftR wi_2  6
      w = wi_16 + s0 + wi_7 + s1
    in
      w :: go (tail xs `snoc` w)

sha512_compress : (block : Vect 128 Bits8) -> (h : Vect 8 Bits64) -> Vect 8 Bits64
sha512_compress block hash_values = zipWith (+) hash_values $ go sha512_round_constants (take _ $ sha512_extend_message $ map (from_be {a = Bits64}) $ group 16 8 block) hash_values
  where
  go : (ks : Vect kn Bits64) -> (ws : Vect kn Bits64) -> (h : Vect 8 Bits64) -> Vect 8 Bits64
  go [] _ h = h
  go (k :: ks) (w :: ws) [a,b,c,d,e,f,g,h] =
    let
      s1 = rotr 14 e `xor` rotr 18 e `xor` rotr 41 e
      ch = (e .&. f) `xor` (complement e .&. g)
      temp1 = h + s1 + ch + k + w
      s0 = rotr 28 a `xor` rotr 34 a `xor` rotr 39 a
      maj = (a .&. b) `xor` (a .&. c) `xor` (b .&. c)
      temp2 = s0 + maj
    in
      go ks ws [temp1 + temp2, a, b, c, d + temp1, e, f, g]

sha512_update : List Bits8 -> Sha512 -> Sha512
sha512_update input (MkSha512 s) =
  let
    Fraction _ 128 nblocks residue_nbyte prf = divMod (s.buffer_nbyte + length input) 128
    (blocks, residue) = splitAt (mult nblocks 128) (replace_vect (sym prf) (s.buffer ++ fromList input))
  in
    MkSha512 $ {buffer := residue, buffer_nbyte := _, buffer_nbyte_constraint := elemSmallerThanBound residue_nbyte }
      ( foldl (\s_, block_ => {hash_values $= sha512_compress block_, npassed_blocks $= S} s_) s (group nblocks 128 blocks) )

sha512_finalize : Sha512 -> Vect 64 Bits8
sha512_finalize (MkSha512 s) =
  concat $ map (to_be {n = 8}) $
    case pad_theorem {block_nbyte = 128} {residue_max_nbyte = 111} {length_nbyte = 16} (LTESucc LTEZero) Refl s.buffer_nbyte_constraint s.buffer (integer_to_be _ $ 8 * (cast s.npassed_blocks * 128 + cast s.buffer_nbyte)) of
      Left block => sha512_compress block s.hash_values
      Right blocks => let (x1, x2) = splitAt 128 blocks in sha512_compress x2 $ sha512_compress x1 s.hash_values

export
Hash Sha512 where
  block_nbyte = 128
  digest_nbyte = 64
  initialize = MkSha512 $ mk_merkle_damgard sha512_init_hash_values
  update = sha512_update
  finalize = sha512_finalize

sha384_init_hash_values : Vect 8 Bits64
sha384_init_hash_values =
  [ 0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939
  , 0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4 ]

export
Hash Sha384 where
  block_nbyte = 128
  digest_nbyte = 48
  initialize = MkSha384 $ MkSha512 $ mk_merkle_damgard sha384_init_hash_values
  update xs (MkSha384 s) = MkSha384 $ update xs s
  finalize (MkSha384 s) = take _ $ finalize s
