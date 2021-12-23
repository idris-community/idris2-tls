module Tests.LSocket

import Control.Linear.Network
import Control.Linear.LIO

okay : LinearIO m => (1 _ : Socket Ready) -> L m ()
okay sock = do
  (Nothing # sock) <- bind sock Nothing 25567
  | (Just bro # sock) => do
    putStrLn $ "error: " <+> show bro
    sock <- close sock
    done sock
  (Nothing # sock) <- listen sock
  | (Just bro # sock) => do
    putStrLn $ "error: " <+> show bro
    sock <- close sock
    done sock
  putStrLn "listening"
  (Nothing # (sock # client)) <- accept sock
  | (Just bro # sock) => do
    putStrLn $ "error: " <+> show bro
    sock <- close sock
    done sock
  (Nothing # client) <- send client "praise allah 100%"
  | (Just bro # client) => do
    putStrLn $ "error: " <+> show bro
    client <- close client
    done client
    close sock >>= done
  close client >>= done
  sock <- close sock
  putStrLn "closed"
  done sock

-- Next Accept  True  = LPair (Socket Listening) (Socket Open)


yako : LinearIO m => SocketError -> L m ()
yako err = do
  putStrLn $ show err

main : LinearIO m => m ()
main = do
  () <- run $ newSocket AF_INET Stream 0 okay yako
  pure ()
