module Crypto.Hash.OID

import Crypto.Hash.Interfaces
import Crypto.Hash
import Data.Vect

{-
  For the nine hash functions mentioned in Appendix B.1, the DER
  encoding T of the DigestInfo value is equal to the following:

  MD2:     (0x)30 20 30 0c 06 08 2a 86 48 86 f7 0d 02 02 05 00 04
               10 || H.
  MD5:     (0x)30 20 30 0c 06 08 2a 86 48 86 f7 0d 02 05 05 00 04
               10 || H.
  SHA-1:   (0x)30 21 30 09 06 05 2b 0e 03 02 1a 05 00 04 14 || H.
  SHA-224:  (0x)30 2d 30 0d 06 09 60 86 48 01 65 03 04 02 04
               05 00 04 1c || H.
  SHA-256: (0x)30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00
               04 20 || H.
  SHA-384: (0x)30 41 30 0d 06 09 60 86 48 01 65 03 04 02 02 05 00
               04 30 || H.
  SHA-512: (0x)30 51 30 0d 06 09 60 86 48 01 65 03 04 02 03 05 00
               04 40 || H.
  SHA-512/224:  (0x)30 2d 30 0d 06 09 60 86 48 01 65 03 04 02 05
                    05 00 04 1c || H.
  SHA-512/256:  (0x)30 31 30 0d 06 09 60 86 48 01 65 03 04 02 06
                    05 00 04 20 || H.
-}

public export
interface Hash algo => RegisteredHash algo where
  header_n_byte : Nat
  header : Vect header_n_byte Bits8

public export
der_digest_n_byte : {algo : _} -> RegisteredHash algo => Nat
der_digest_n_byte = header_n_byte {algo} + digest_nbyte {algo}

export
hashWithHeader : {algo : _} -> RegisteredHash algo => List Bits8 -> Vect (der_digest_n_byte {algo}) Bits8
hashWithHeader plaintext = header {algo} ++ hash algo plaintext

public export
RegisteredHash Sha1 where
  header_n_byte = 15
  header = [ 0x30, 0x21, 0x30, 0x09, 0x06, 0x05, 0x2b, 0x0e, 0x03, 0x02, 0x1a, 0x05, 0x00, 0x04, 0x14 ]

public export
RegisteredHash Sha256 where
  header_n_byte = 19
  header = [ 0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20 ]

public export
RegisteredHash Sha384 where
  header_n_byte = 19
  header = [ 0x30, 0x41, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02, 0x05, 0x00, 0x04, 0x30 ]

public export
RegisteredHash Sha512 where
  header_n_byte = 19
  header = [ 0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03, 0x05, 0x00, 0x04, 0x40 ]
