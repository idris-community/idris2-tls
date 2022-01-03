module Crypto.Hash.MerkleDamgard

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

public export
record MerkleDamgard (internal_state_nbyte : Nat) (0 block_nbyte : Nat) (0 word_type : Type) where
  constructor MkMerkleDamgard
  hash_values : Vect internal_state_nbyte word_type
  buffer_nbyte : Nat
  buffer_nbyte_constraint : LT buffer_nbyte block_nbyte
  buffer : Vect buffer_nbyte Bits8
  npassed_blocks : Nat

export
mk_merkle_damgard : (init_hash_values : Vect internal_state_nbyte word_type) ->
                    {auto 0 prf : LTE 1 block_nbyte} ->
                    MerkleDamgard internal_state_nbyte block_nbyte word_type
mk_merkle_damgard x {prf = LTESucc prf'} = MkMerkleDamgard x 0 (LTESucc LTEZero) [] 0

public export
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

public export
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

public export
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

public export
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

public export
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
