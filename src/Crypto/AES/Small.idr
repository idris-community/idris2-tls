-- Direct translation of AES specification
-- Kept as a reference

module Crypto.AES.Small

import Crypto.AES.Common
import Data.Bits
import Data.DPair
import Data.Fin
import Data.List
import Data.Nat
import Data.Stream
import Data.Vect
import Utils.Misc
import Utils.Bytes

mk_round_keys : {n_k, n_b : _} -> {auto 0 ok : NonZero n_b} -> {auto 0 ok2 : NonZero n_k} -> (n_main_rounds : Nat) -> (key : Vect n_k (Vect n_b Bits8)) -> (Vect 4 (Vect n_b Bits8), Vect n_main_rounds (Vect 4 (Vect n_b Bits8)), Vect 4 (Vect n_b Bits8))
mk_round_keys n_main_rounds k =
  let
    (rk_init :: rks) = Stream.take (S (S n_main_rounds)) $ chunk _ $ prepend (toList k) $ expand_key k
  in
    (rk_init, unsnoc rks)

encrypt_block' : {n_k : _} -> {auto 0 ok : NonZero n_k} -> (n_main_rounds : Nat) -> (key : Vect n_k (Vect 4 Bits8)) -> (state : Vect 4 (Vect 4 Bits8)) -> Vect 4 (Vect 4 Bits8)
encrypt_block' n_main_rounds k x =
  let
    (init_rk, main_rks, final_rk) = mk_round_keys n_main_rounds k
    -- initial round
    x = matxor x init_rk
    -- main rounds
    x = foldl (flip $ \rk => matxor rk . mix_columns . shift_rows . sub_bytes) x main_rks
    -- final round
    x = matxor final_rk $ shift_rows $ sub_bytes x
  in
    x

export
encrypt_block : (mode : Mode) -> (key : Vect ((get_n_k mode) * 4) Bits8) -> (state : Vect 16 Bits8) -> Vect 16 Bits8
encrypt_block mode k s = concat $ encrypt_block' {ok = n_k_never_Z mode} (get_main_rounds mode) (group _ _ k) (group _ _ s)

decrypt_block' : {n_k : _} -> {auto 0 ok : NonZero n_k} -> (n_main_rounds : Nat) -> (key : Vect n_k (Vect 4 Bits8)) -> (state : Vect 4 (Vect 4 Bits8)) -> Vect 4 (Vect 4 Bits8)
decrypt_block' n_main_rounds k x =
  let
    (init_rk, main_rks, final_rk) = mk_round_keys n_main_rounds k
    -- initial round
    x = matxor x init_rk
    -- main rounds
    x = foldl (flip $ \rk => inv_mix_columns . matxor rk . inv_sub_bytes . inv_shift_rows) x main_rks
    -- final round
    x = matxor final_rk $ inv_sub_bytes $ inv_shift_rows x
  in
    x

export
decrypt_block : (mode : Mode) -> (key : Vect ((get_n_k mode) * 4) Bits8) -> (state : Vect 16 Bits8) -> Vect 16 Bits8
decrypt_block mode k x = concat $ decrypt_block' {ok = n_k_never_Z mode} (get_main_rounds mode) (group _ _ k) (group _ _ x)
