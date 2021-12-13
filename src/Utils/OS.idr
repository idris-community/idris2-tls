module Utils.OS

import Data.Buffer
import System.FFI
import System.Info
import Data.List

%foreign "C:uname,libc"
prim_io__uname : Buffer -> PrimIO Int

public export
data OS : Type where
  Windows : OS
  Linux   : OS
  Darwin  : OS
  Unix    : OS

public export
Show OS where
  show Windows = "windows"
  show Linux   = "linux"
  show Darwin  = "darwin"
  show Unix    = "unix"

uname' : HasIO m => Buffer -> m String
uname' buf = do 
  _ <- primIO $ prim_io__uname buf
  str <- getString buf 0 65
  pure $ pack $ takeWhile (/= '\NUL') $ unpack str

uname : Maybe String
uname = unsafePerformIO $ do
  buf' <- newBuffer 65
  case buf' of
    Just buf => Just <$> uname' buf
    Nothing => pure Nothing

public export
detect_platform : Maybe OS
detect_platform =
  if isWindows then Just Windows else
    case os of
      "darwin" => Just Darwin
      "unix" => 
        case uname of
          Just "Linux" => Just Linux
          Just _ => Just Unix
          _ => Nothing
      _ => Nothing
