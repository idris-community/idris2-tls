module Network.TLS.HKDF

import Crypto.Hash
import Data.Bits
import Data.List
import Data.Stream
import Data.Stream.Extra
import Data.Vect
import Utils.Bytes
import Utils.Misc

import Debug.Trace

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
record HandshakeKeys (iv : Nat) (key : Nat) where
  constructor MkHandshakeKeys 
  handshake_secret : List Bits8
  client_handshake_key : Vect key Bits8
  server_handshake_key : Vect key Bits8
  client_handshake_iv  : Vect iv Bits8
  server_handshake_iv  : Vect iv Bits8
  client_traffic_secret : List Bits8
  server_traffic_secret : List Bits8

public export
record ApplicationKeys (iv : Nat) (key : Nat) where
  constructor MkApplicationKeys
  client_application_key : Vect key Bits8
  server_application_key : Vect key Bits8
  client_application_iv  : Vect iv Bits8
  server_application_iv  : Vect iv Bits8

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
tls13_application_derive : {iv : Nat} -> {key : Nat} -> (0 algo : Type) -> Hash algo => HandshakeKeys iv key -> List Bits8 -> ApplicationKeys iv key
tls13_application_derive algo (MkHandshakeKeys handshake_secret _ _ _ _ _ _) handshake_hash =
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

public export
record Application2Keys (iv : Nat) (key : Nat) (mac : Nat) where
  constructor MkApplication2Keys
  master_secret : Vect 48 Bits8
  client_mac_key : Vect mac Bits8
  server_mac_key : Vect mac Bits8
  client_application_key : Vect key Bits8
  server_application_key : Vect key Bits8
  client_application_iv  : Vect iv  Bits8
  server_application_iv  : Vect iv  Bits8

hmac_stream : (0 algo : Type) -> Hash algo => List Bits8 -> List Bits8 -> Stream Bits8
hmac_stream algo secret seed =
  stream_concat
  $ map (\ax => toList $ hmac algo secret $ ax <+> seed)
  $ drop 1
  $ iterate (toList . hmac algo secret) seed

public export
tls12_application_derive : (0 algo : Type) -> Hash algo => (iv : Nat) -> (key : Nat) -> (mac : Nat) -> List Bits8 -> List Bits8 -> List Bits8 ->
                           Application2Keys iv key mac
tls12_application_derive algo iv key mac shared_secret client_random server_random =
  let master_secret =
        trace ("server random: " <+> xxd server_random)
        $ trace ("client random: " <+> xxd client_random)
        $ trace ("shared secret: " <+> xxd shared_secret)
        $ Stream.take 48
        $ hmac_stream algo shared_secret
        $ (encode_ascii "master secret") <+> client_random <+> server_random
      secret_material =
        hmac_stream algo
          (trace ("master secret: " <+> (xxd $ toList master_secret)) (toList master_secret))
          (encode_ascii "key expansion" <+> server_random <+> client_random)
      (client_mac_key, secret_material)         = Misc.splitAt mac secret_material
      (server_mac_key, secret_material)         = Misc.splitAt mac secret_material
      (client_application_key, secret_material) = Misc.splitAt key secret_material
      (server_application_key, secret_material) = Misc.splitAt key secret_material
      (client_application_iv, secret_material)  = Misc.splitAt iv  secret_material
      (server_application_iv, secret_material)  = Misc.splitAt iv  secret_material
  in MkApplication2Keys
       master_secret
       client_mac_key
       server_mac_key
       (trace ("c_ap_k: " <+> (xxd $ toList client_application_key)) $ client_application_key)
       server_application_key
       (trace ("c_ap_iv: " <+> (xxd $ toList client_application_iv)) $ client_application_iv)
       server_application_iv

public export
tls12_verify_data : (0 algo : Type) -> Hash algo => (n : Nat) -> List Bits8 -> List Bits8 -> Vect n Bits8
tls12_verify_data algo n master_secret records_hash =
  take _ $ hmac_stream algo master_secret (encode_ascii "client finished" <+> records_hash)

--- TESTS

test_premaster_secret : List Bits8
test_premaster_secret =
  [ 0x03, 0x03, 0x24, 0x43, 0x41, 0x41, 0x46, 0xd9, 0xde, 0xda, 0x55, 0x11, 0xb0, 0xb9, 0xa4, 0xd4, 0xcc, 0x42, 0x5a, 0x21, 0x70
  , 0xaa, 0xb3, 0x30, 0x1f, 0x58, 0x4f, 0xf1, 0xea, 0x1d, 0x4f, 0x58, 0xab, 0x42, 0x8c, 0x9c, 0x30, 0x62, 0x70, 0xe2, 0x15, 0x41
  , 0x99, 0x1a, 0x39, 0xa7, 0x60, 0x00 ]

test_client_random : List Bits8
test_client_random =
  [ 0xdf, 0x2d, 0xbc, 0x93, 0x11, 0xf2, 0xb2, 0x69, 0x2b, 0xcf, 0xf6, 0x04, 0x57, 0x61, 0xbd, 0x35, 0x97, 0x56, 0x0f, 0x3b, 0x84
  , 0x97, 0x8f, 0x59, 0xe7, 0xf4, 0x56, 0x2d, 0x9e, 0x39, 0x83, 0x66 ]

test_server_random : List Bits8
test_server_random =
  [ 0xc4, 0xd8, 0x87, 0xca, 0x6d, 0xd1, 0x53, 0xa3, 0xb3, 0xe0, 0xba, 0xbb, 0x4a, 0x68, 0x50, 0xc7, 0xdc, 0x48, 0xc9, 0x2c, 0x8c
  , 0x20, 0xa3, 0x82, 0x44, 0x4f, 0x57, 0x4e, 0x47, 0x52, 0x44, 0x01 ]

test_client_random2 : List Bits8
test_client_random2 = 
  [ 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07
  , 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f
  , 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17
  , 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f
  ]

test_server_random2 : List Bits8
test_server_random2 =
  [ 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77
  , 0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f
  , 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87
  , 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f
  ]

test_premaster_secret2 : List Bits8
test_premaster_secret2 =
  [ 0xdf, 0x4a, 0x29, 0x1b, 0xaa, 0x1e, 0xb7, 0xcf, 0xa6, 0x93, 0x4b, 0x29, 0xb4, 0x74, 0xba, 0xad, 0x26, 0x97, 0xe2, 0x9f, 0x1f
  , 0x92, 0x0d, 0xcc, 0x77, 0xc8, 0xa0, 0xa0, 0x88, 0x44, 0x76, 0x24 ]

test_master_secret : Vect 48 Bits8
test_master_secret =
  Stream.take 48
  $ hmac_stream Sha256 test_premaster_secret2
  $ (encode_ascii "master secret") <+> test_client_random2 <+> test_server_random2
