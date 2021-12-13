module Crypto.HKDF

import Crypto.Hash
import Data.Bits
import Data.List
import Data.Stream
import Data.Stream.Extra
import Data.Vect
import Utils.Bytes
import Utils.Misc

public export
hkdf_extract : (0 algo : Type) -> Hash algo => List Bits8 -> List Bits8 -> Vect (digest_nbyte {algo}) Bits8
hkdf_extract algo salt ikm = hmac algo salt ikm

hkdf_expand_stream : (0 algo : Type) -> Hash algo => List Bits8 -> List Bits8 -> Stream Bits8
hkdf_expand_stream algo prk info = stream_concat (snd <$> iterate go (Z, []))
  where
    go : (Nat, List Bits8) -> (Nat, List Bits8)
    go (i, last) = 
      let i' = cast {to=Bits8} (S i)
          body = last ++ info ++ [i']
      in (S i, toList $ hmac algo prk body)

public export
hkdf_expand : (0 algo : Type) -> Hash algo => (l : Nat) -> List Bits8 -> List Bits8 -> Vect l Bits8
hkdf_expand algo l prk info = take l $ hkdf_expand_stream algo prk info

tls13_constant : List Bits8
tls13_constant = encode_ascii "tls13 "

export
tls13_hkdf_expand_label : (0 algo : Type) -> Hash algo => (secret : List Bits8) -> (label : List Bits8) -> (context : List Bits8) -> (length : Nat) -> Vect length Bits8
tls13_hkdf_expand_label algo secret label context lth =
  let l = to_be {n=2} $ cast {to=Bits16} lth
      l' = cast {to=Bits8} $ (6 + length label)
      i' = cast {to=Bits8} $ length context
      body = ((toList l) <+> [l'] <+> tls13_constant <+> label <+> [i'] <+> context)
  in hkdf_expand algo lth secret body

public export
data HandshakeKeys : (iv : Nat) -> (key : Nat) -> Type where
  MkHandshakeKeys : List Bits8 ->
                    {iv, key : Nat} ->
                    (client_handshake_key : Vect key Bits8) ->
                    (server_handshake_key : Vect key Bits8) ->
                    (client_handshake_iv  : Vect iv  Bits8) ->
                    (server_handshake_iv  : Vect iv  Bits8) ->
                    (client_traffic_secret : List Bits8) ->
                    (server_traffic_secret : List Bits8) ->
                    HandshakeKeys iv key

public export
data ApplicationKeys : (iv : Nat) -> (key : Nat) -> Type where
  MkApplicationKeys : {iv,key : Nat} ->
                      (client_application_key : Vect key Bits8) ->
                      (server_application_key : Vect key Bits8) ->
                      (client_application_iv  : Vect iv  Bits8) ->
                      (server_application_iv  : Vect iv  Bits8) ->
                      ApplicationKeys iv key

export
tls13_handshake_derive : (0 algo : Type) -> Hash algo => (iv : Nat) -> (key : Nat) -> List Bits8 -> List Bits8 -> HandshakeKeys iv key
tls13_handshake_derive algo iv key shared_secret hello_hash =
  let zeros = List.replicate (digest_nbyte {algo}) (the Bits8 0)
      early_secret = toList $ hkdf_extract algo [the Bits8 0] zeros
      empty_hash = toList $ hash algo []
      derived_secret = tls13_hkdf_expand_label algo early_secret (encode_ascii "derived") empty_hash $ digest_nbyte {algo}
      handshake_secret = toList $ hkdf_extract algo (toList derived_secret) shared_secret
      client_handshake_traffic_secret = toList $
        tls13_hkdf_expand_label algo handshake_secret (encode_ascii "c hs traffic") hello_hash $ digest_nbyte {algo}
      server_handshake_traffic_secret = toList $
        tls13_hkdf_expand_label algo handshake_secret (encode_ascii "s hs traffic") hello_hash $ digest_nbyte {algo}
      client_handshake_key =
        tls13_hkdf_expand_label algo client_handshake_traffic_secret (encode_ascii "key") [] key
      client_handshake_iv =
        tls13_hkdf_expand_label algo client_handshake_traffic_secret (encode_ascii "iv") [] iv
      server_handshake_key =
        tls13_hkdf_expand_label algo server_handshake_traffic_secret (encode_ascii "key") [] key
      server_handshake_iv =
        tls13_hkdf_expand_label algo server_handshake_traffic_secret (encode_ascii "iv") [] iv
  in MkHandshakeKeys
      handshake_secret
      client_handshake_key
      server_handshake_key
      client_handshake_iv
      server_handshake_iv
      (toList client_handshake_traffic_secret)
      (toList server_handshake_traffic_secret)

public export
tls13_application_derive : (0 algo : Type) -> Hash algo => HandshakeKeys iv key -> List Bits8 -> ApplicationKeys iv key
tls13_application_derive algo {iv} {key} (MkHandshakeKeys handshake_secret _ _ _ _ _ _) handshake_hash =
  let zeros = List.replicate (digest_nbyte {algo}) (the Bits8 0)
      empty_hash = toList $ hash algo []
      derived_secret = 
        tls13_hkdf_expand_label algo handshake_secret (encode_ascii "derived") empty_hash $ digest_nbyte {algo}
      master_secret = toList $ hkdf_extract algo (toList derived_secret) zeros
      client_application_traffic_secret = toList $
        tls13_hkdf_expand_label algo master_secret (encode_ascii "c ap traffic") handshake_hash $ digest_nbyte {algo}
      server_application_traffic_secret = toList $
        tls13_hkdf_expand_label algo master_secret (encode_ascii "s ap traffic") handshake_hash $ digest_nbyte {algo}
      client_application_key =
        tls13_hkdf_expand_label algo client_application_traffic_secret (encode_ascii "key") [] key
      client_application_iv =
        tls13_hkdf_expand_label algo client_application_traffic_secret (encode_ascii "iv") [] iv
      server_application_key =
        tls13_hkdf_expand_label algo server_application_traffic_secret (encode_ascii "key") [] key
      server_application_iv =
        tls13_hkdf_expand_label algo server_application_traffic_secret (encode_ascii "iv") [] iv
  in MkApplicationKeys client_application_key server_application_key client_application_iv server_application_iv

public export
tls13_verify_data : (0 algo : Type) -> Hash algo => List Bits8 -> List Bits8 -> List Bits8
tls13_verify_data algo traffic_secret records_hash =
  let finished_key = toList $
        tls13_hkdf_expand_label algo traffic_secret (encode_ascii "finished") [] $ digest_nbyte {algo}
  in toList $ hkdf_extract algo finished_key records_hash
