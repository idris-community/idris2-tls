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

record Sha (0 block_nbyte : Nat) (0 word_type : Type) where
  constructor MkSha
  hash_values : Vect 5 word_type
  buffer_nbyte : Nat
  buffer_nbyte_constraint : LT buffer_nbyte block_nbyte
  buffer : Vect buffer_nbyte Bits8
  npassed_blocks : Nat

export
data Sha1 : Type where
  MkSha1 : Sha 64 Bits32 -> Sha1

mk_sha : (init_hash_values : Vect 5 word_type) -> {auto 0 prf : LTE 1 block_nbyte} -> Sha block_nbyte word_type
mk_sha x {prf = LTESucc prf'} = MkSha x 0 (LTESucc LTEZero) [] 0

pad_lemma : {residue_nbyte, length_nbyte, residue_max_nbyte, block_nbyte : Nat}
  -> LTE 1 block_nbyte
  -> (residue_max_nbyte + 1 + length_nbyte = block_nbyte)
  -> LTE residue_nbyte residue_max_nbyte
  -> (plus residue_nbyte (S (plus (minus residue_max_nbyte residue_nbyte) length_nbyte))) = block_nbyte
pad_lemma remilia flandre sakuya =
  rewrite sym flandre in
  rewrite sym $ plusSuccRightSucc residue_nbyte (plus (minus residue_max_nbyte residue_nbyte) length_nbyte) in
  rewrite plusAssociative residue_nbyte (minus residue_max_nbyte residue_nbyte) length_nbyte in
  rewrite plusCommutative residue_nbyte (minus residue_max_nbyte residue_nbyte) in
  rewrite plusMinusLte residue_nbyte residue_max_nbyte sakuya in
  rewrite plusCommutative residue_max_nbyte 1 in
    Refl

pad_over_lemma : {residue_nbyte, length_nbyte, residue_max_nbyte, block_nbyte : Nat}
  -> (residue_max_nbyte + 1 + length_nbyte = block_nbyte)
  -> LT residue_nbyte block_nbyte
  -> plus residue_nbyte (S (plus (plus (minus block_nbyte residue_nbyte) residue_max_nbyte) length_nbyte)) = (plus block_nbyte (plus block_nbyte 0))
pad_over_lemma flandre cirno =
  rewrite sym $ plusSuccRightSucc residue_nbyte (plus (plus (minus block_nbyte residue_nbyte) residue_max_nbyte) length_nbyte) in
  rewrite plusAssociative residue_nbyte (plus (minus block_nbyte residue_nbyte) residue_max_nbyte) length_nbyte in
  rewrite plusAssociative residue_nbyte (minus block_nbyte residue_nbyte) residue_max_nbyte in
  rewrite plusCommutative residue_nbyte (minus block_nbyte residue_nbyte) in
  rewrite plusMinusLte residue_nbyte block_nbyte (lteSuccLeft cirno) in
  rewrite sym $ plusAssociative block_nbyte residue_max_nbyte length_nbyte in
  rewrite plusSuccRightSucc block_nbyte (plus residue_max_nbyte length_nbyte) in
  rewrite plusZeroRightNeutral block_nbyte in
  rewrite flandre' in
    Refl
  where
  flandre' : S (plus residue_max_nbyte length_nbyte) = block_nbyte
  flandre' = rewrite sym flandre in rewrite plusCommutative residue_max_nbyte 1 in Refl

pad_residue : {residue_nbyte, length_nbyte, residue_max_nbyte, block_nbyte : _}
  -> (0 _ : LTE 1 block_nbyte)
  -> (0 _ : (residue_max_nbyte + 1 + length_nbyte = block_nbyte))
  -> (0 _ : LTE residue_nbyte residue_max_nbyte)
  -> Vect residue_nbyte Bits8
  -> Vect length_nbyte Bits8
  -> Vect block_nbyte Bits8
pad_residue remilia flandre sakuya residue b_length =
   replace_vect (pad_lemma remilia flandre sakuya) $
     residue
     ++ [0b10000000]
     ++ replicate (minus residue_max_nbyte residue_nbyte) 0
     ++ b_length

pad_over_residue : {residue_nbyte, length_nbyte, residue_max_nbyte, block_nbyte : _}
  -> (0 _ : LTE 1 block_nbyte)
  -> (0 _ : residue_max_nbyte + 1 + length_nbyte = block_nbyte)
  -> (0 _ : LT residue_max_nbyte residue_nbyte)
  -> (0 _ : LT residue_nbyte block_nbyte)
  -> Vect residue_nbyte Bits8
  -> Vect length_nbyte Bits8
  -> Vect (2 * block_nbyte) Bits8
pad_over_residue remilia flandre rumia cirno residue b_length =
  replace_vect (pad_over_lemma flandre cirno) $
    residue
    ++ [0b10000000]
    ++ replicate (minus block_nbyte residue_nbyte + residue_max_nbyte) 0
    ++ b_length

pad_theorem : {residue_nbyte, length_nbyte, residue_max_nbyte, block_nbyte : _}
  -> (0 _ : LTE 1 block_nbyte)
  -> (0 _ : residue_max_nbyte + 1 + length_nbyte = block_nbyte)
  -> (0 _ : LT residue_nbyte block_nbyte)
  -> Vect residue_nbyte Bits8
  -> Vect length_nbyte Bits8
  -> Either (Vect block_nbyte Bits8) (Vect (block_nbyte + block_nbyte) Bits8)
pad_theorem remilia flandre cirno input b_length =
  case isLTE residue_nbyte residue_max_nbyte of
    Yes sakuya => Left $ pad_residue remilia flandre sakuya input b_length
    No rumia => Right $ replace_vect (cong (plus block_nbyte) (plusZeroRightNeutral block_nbyte)) $ pad_over_residue remilia flandre (notLTEImpliesGT rumia) cirno input b_length

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
Hash Sha1 where
  block_nbyte = 64
  digest_nbyte = 20
  initialize = MkSha1 $ mk_sha sha1_init_hash_values
  update = sha1_update
  finalize = sha1_finalize
