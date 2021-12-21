module Crypto.ChaCha

import Control.Monad.State
import Data.Bits
import Data.DPair
import Data.Fin
import Data.Nat.Order.Properties
import Data.Vect
import Utils.Bytes
import Utils.Misc

public export
Key : Type
Key = Vect 8 Bits32 -- 32 * 8 = 256

public export
ChaChaState : Type
ChaChaState = Vect 16 Bits32

-- The first four words (0-3) are constants
public export
constants : Vect 4 Bits32
constants = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] -- ['expa', 'nd 3', '2-by', 'te k']

public export
rotl : Subset Nat (`LT` 32) -> Bits32 -> Bits32
rotl b'@(Element Z p) a = a
rotl b'@(Element (S b) p) a = shiftL a (subset_to_fin b') .|. shiftR a (subset_to_fin $ Element (minus 31 b) $ LTESucc (minusLTE b 31))

public export
quarter_rotate : Fin 16 -> Fin 16 -> Fin 16 -> Fin 16 -> State ChaChaState ()
quarter_rotate a b c d = do
  modify (\s => updateAt a (+ index b s) s)
  modify (\s => updateAt d (`xor` index a s) s)
  modify (\s => updateAt d (rotl $ Element 16 (lteAddRight _)) s)

  modify (\s => updateAt c (+ index d s) s)
  modify (\s => updateAt b (`xor` index c s) s)
  modify (\s => updateAt b (rotl $ Element 12 (lteAddRight _)) s)

  modify (\s => updateAt a (+ index b s) s)
  modify (\s => updateAt d (`xor` index a s) s)
  modify (\s => updateAt d (rotl $ Element 8 (lteAddRight _)) s)

  modify (\s => updateAt c (+ index d s) s)
  modify (\s => updateAt b (`xor` index c s) s)
  modify (\s => updateAt b (rotl $ Element 7 (lteAddRight _)) s)

public export
double_rotate : State ChaChaState ()
double_rotate = do
  quarter_rotate 0 4  8 12
  quarter_rotate 1 5  9 13
  quarter_rotate 2 6 10 14
  quarter_rotate 3 7 11 15
  ------------------------
  quarter_rotate 0 5 10 15
  quarter_rotate 1 6 11 12
  quarter_rotate 2 7  8 13
  quarter_rotate 3 4  9 14

public export
run2x : (n_double_rounds : Nat) -> ChaChaState -> ChaChaState
run2x n_double_rounds s =
  execState s $ do
    original <- get
    go last
    modify (zipWith (+) original)
  where
  go : Fin (S n_double_rounds) -> State ChaChaState ()
  go FZ = pure ()
  go (FS wit) = double_rotate *> go (weaken wit)

||| ChaCha construction with 4 octets counter and 12 octets nonce as per RFC8439
public export
chacha_rfc8439_block : Nat -> (counter : Bits32) -> Key -> Vect 3 Bits32 -> Vect 64 Bits8
chacha_rfc8439_block rounds counter key nonce = concat $ map (to_le {n = 4}) $ run2x rounds $ constants ++ key ++ [counter] ++ nonce

||| ChaCha construction with 8 octets counter and 8 octets nonce as per the original ChaCha specification
public export
chacha_original_block : Nat -> (counter : Bits64) -> Key -> Vect 2 Bits32 -> Vect 64 Bits8
chacha_original_block rounds counter key nonce = concat $ map (to_le {n = 4}) $ run2x rounds $ constants ++ key ++ split_word counter ++ nonce
  where
    split_word : Bits64 -> Vect 2 Bits32
    split_word a = [ cast a, cast (shiftR a 32) ]
