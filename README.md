# idris2-tls
A portable idris2 implementation of TLS 1.2 and TLS 1.3 protocol.

# Goal
This library aims to provide a TLS implementation in Idris that supports communication with most modern websites and provide reasonable performance.
Not meant for production. Read the notes on security.

# Example
An example of how the TLS socket is used can be found [here](src/Tests/LTLS.idr).
More examples on how to use the internal modules can be found in the [Tests](src/Tests) folder.

# Support coverage
The library currently supports the following cipher suites:

TLS 1.3:
- TLS_AES_128_GCM_SHA256
- TLS_AES_256_GCM_SHA384
- TLS_CHACHA20_POLY1305_SHA256

TLS 1.2:
- TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
- TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
- TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
- TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
- TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256
- TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256

The library currently supports the following groups for key exchange during TLS handshake:
- X25519
- SECP256r1
- SECP384r1

The following groups are implemented, but not used in the linear TLS handle abstraction.
- X448
- SECP521r1

If you want to use these groups for key exchange, you would need to use the lower level TLS state abstraction. An
example of how it would be done is in [TLS.idr](src/Tests/TLS.idr).

Since most modern websites support key exchange with elliptic curves (and I can't figure out how RSA parameters are encoded), 
RSA key exchange is not supported, nor do we consider implementing it by ourselves anytime soon.
However, we may consider doing so in the future if there is enough demand.

Other symmetric ciphers such as Camilla, ARIA, DES, RC4 are not implemented, nor do we plan to implement them, because they are either deprecated 
or way too obscure.

Right now only GCM is implemented for AES mode of operation. We may implement other mode of operation such as CBC in the future, but it is not on our timeline
since GCM seems to cover most websites.

Older TLS versions such as TLS 1.0, TLS 1.1 and SSL will not be implemented since they are way too obscure and insecure. 

Any PRs that implement new ciphers, mode of operations, curves, key exchange schemes (like RSA) are **extremely** welcomed.

# Note on bindings
While we try to minimize the amount of bindings as much as possible, they are still needed in order to provide cryptographically secure random entropy.
The base Idris library has `System.Random`, but it is not cryptographically random, so we had to resort to using bindings.

Currently bindings for random entropy are implemented for C, Scheme and JS backends. Note that for some platforms they had not been tested, so any feedback
would be appreciated. A current outline of what bindings are used is as follow:

C / Scheme:
- Windows: `SystemPrng` (not tested)
- MacOS: `arc4random_buf` (not tested)
- Linux: `getrandom` (tested on `GNU/Linux 5.15.10-gentoo` by tensorknower69)
- Other systems: `arc4random_buf` (tested on OpenBSD by octeep, not tested on other systems)

On Unix-like systems, `/dev/urandom` and `/dev/random` are decidedly not used because I've encountered blocking problems with them, so I figured that directly
using syscalls would be cleaner.

Node / Javascript:
- Node: `require('crypto').randomBytes` (tested)
- Other environments: `crypto.getRandomValues` (not tested)

If you have tested the `MonadRandom IO` implementation on any platforms which we have not tested, feel free to open a PR and change this `README.md`.

If your own implementation of `MonadRandom IO` for whatever reasons, an example of how they are implemented can be found [here](src/Crypto/Random).

We have also implemented our own bindings and library for C networking. The official network library is decidedly not used because it uses `String` for
payloads. This makes handling NUL bytes extremely difficult since `String` is NUL terminated. Therefore, we made our own bindings which uses `List Bits8`
instead. Other solutions to this problem are welcomed.

# Other notes
We have decidedly not use any bytes library and rely heavily on `List Bits8`, `Vect n Bits8` instead. We feel that this approach is more pure and functional
and in general more pleasing to work with. While other bytes library may yield better performance, we feel that our approach performs reasonably well.

# Notes on security
**This project does not guarantee security**. Our implementations may be flawed with exploitable bugs. 
Our cryptographic primitives are most definitely vulnerable to all sorts of side channel attack, 
e.g. [timing attack](https://en.wikipedia.org/wiki/Timing_attack). The code has not been audited at all, and the authors
have zero background in cryptography nor cybersecurity. Do not use this under the assumption that it is secure. Use at your own risk.

# TODO
- Certificate parsing
- Verifying handshake keys with certificate
- Certificate chain verification
- OCSP stapling

# License
This project is licensed under the ISC license. See [LICENSE](LICENSE).
