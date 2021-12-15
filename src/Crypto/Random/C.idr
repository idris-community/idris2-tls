module Crypto.Random.C

import Crypto.Random
import System.FFI
import Data.Vect
import Utils.Misc
import Utils.Misc.C
import Data.Buffer
import Data.List
import System.Info

-- Needed to distinguish Linux from other Unix-like systems
%foreign "C:uname,libc"
prim_io__uname : Buffer -> PrimIO Int

%foreign "C:arc4random_buf,libc"
prim_io__arc4random_buf : AnyPtr -> Int -> PrimIO ()

%foreign "C:getrandom,libc"
prim_io__getrandom_buf : AnyPtr -> Int -> Int -> PrimIO ()

-- TODO: Test this
%foreign "C:SystemPrng,libc"
prim_io__systemprng : AnyPtr -> Int -> PrimIO ()

anyptr_content : HasIO io => (AnyPtr -> Int -> PrimIO ()) -> (n : Nat) -> io (Vect n Bits8)
anyptr_content f n = do
  let n' = cast n
  pointer <- malloc n'
  primIO $ f pointer n'
  r <- peek_bytes pointer 0 n
  free pointer
  pure r

data Platform : Type where
  Windows : Platform
  Linux   : Platform
  Darwin  : Platform
  Unix    : Platform

uname' : Buffer -> IO String
uname' buf = do
  _ <- primIO $ prim_io__uname buf
  str <- getString buf 0 65
  pure $ pack $ takeWhile (/= '\NUL') $ unpack str

uname : Maybe String
uname = unsafePerformIO $ do
  buf' <- newBuffer 257
  case buf' of
    Just buf => Just <$> uname' buf
    Nothing => pure Nothing

detect_os : Maybe Platform
detect_os =
  if isWindows then Just Windows else
    case os of
      "darwin" => Just Darwin
      "unix" =>
         case uname of
           Just "Linux" => Just Linux
           Just _ => Just Unix
           _ => Nothing
      _ => Nothing

public export
HasIO io => MonadRandom io where
  random_bytes Z = pure []
  random_bytes n =
  case detect_os of
    Just Darwin => anyptr_content prim_io__arc4random_buf n
    Just Unix   => anyptr_content prim_io__arc4random_buf n
    Just Linux  => anyptr_content (\p,n => prim_io__getrandom_buf p n 0) n
    Just Windows => anyptr_content prim_io__systemprng n
    _ => assert_total $ idris_crash "no random backend availible"
