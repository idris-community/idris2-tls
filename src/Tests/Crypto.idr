module Tests.Crypto

import Control.Monad.State
import Crypto.RSA
import Crypto.Random
import Crypto.Random.C
import Data.Vect

test_chacha : HasIO m => m ()
test_chacha = do
  drg <- new_chacha12_drg
  let a = evalState drg (random_bytes 1024)
  putStrLn $ show a

test_rsa : HasIO m => m Integer
test_rsa = do
  (pk, sk) <- generate_key_pair 1024
  let m = 42069
  let c = rsa_encrypt pk m
  rsa_decrypt_blinded sk c
