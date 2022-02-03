module CertTest

import Network.TLS.Certificate.System
import Network.TLS.Certificate
import Control.Monad.Error.Either

export
test_cert : EitherT String IO ()
test_cert = do
  certs <- MkEitherT get_system_trusted_certs
  putStrLn "\{show (length certs)} certificates found"
