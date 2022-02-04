#include <stdlib.h>

#if defined(_WIN32) || defined(_WIN64)
#define __WINDOWS__ 1
#endif

#ifdef __linux__
#include <sys/random.h>
#endif

#if __WINDOWS__
#include <winsock2.h>
#include <windows.h>
#include <wincrypt.h>
#include <bcrypt.h>
#include <stdint.h>
#else
#include <sys/socket.h>
#endif

int random_buf(void *buf, size_t nbytes) {
#ifdef __linux__
    ssize_t out = getrandom(buf, nbytes, 0);
    return out < 0;
#elif __WINDOWS__
    NTSTATUS status = BCryptGenRandom(NULL, buf, nbytes, BCRYPT_USE_SYSTEM_PREFERRED_RNG);
    return !BCRYPT_SUCCESS(status);
#else
    arc4random_buf(buf, nbytes);
    return 0;
#endif
}

ssize_t sock_send(int s, const void *msg, size_t len, int flags) {
    return send(s, msg, len, flags);
}

ssize_t sock_recv(int s, void *buf, size_t len, int flags) {
    return recv(s, buf, len, flags);
}

#ifdef __WINDOWS__
void* openCertStore() {
    return CertOpenSystemStoreA(0, "ROOT");
}

int closeCertStore(void* hCertStore) {
    return CertCloseStore(hCertStore, 0);
}

const void* nextCertInStore(void* hCertStore, void* prevCert) {
    return CertEnumCertificatesInStore(hCertStore, prevCert);
}

int32_t certLenInfo(PCCERT_CONTEXT cert) {
    if (cert->dwCertEncodingType != 1) {
        return -1;
    }

    return cert->cbCertEncoded;
}

void certBody(PCCERT_CONTEXT cert, void* buf) {
    memcpy(buf, cert->pbCertEncoded, cert->cbCertEncoded);
}
#endif
