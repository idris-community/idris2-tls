#include <stdlib.h>
#ifdef __linux__
#include <sys/random.h>
#elif _WIN64
#include <windows.h>
#include <ntstatus.h>
#include <winerror.h>
#include <bcrypt.h>
#elif _WIN32
#include <windows.h>
#include <ntstatus.h>
#include <winerror.h>
#include <bcrypt.h>
#endif

int random_buf(void *buf, size_t nbytes) {
#ifdef __linux__
    ssize_t out = getrandom(buf, nbytes, 0);
    return out < 0;
#elif _WIN64
    NTSTATUS status = BCryptGenRandom(NULL, buf, nbytes, BCRYPT_USE_SYSTEM_PREFERRED_RNG);
    return !BCRYPT_SUCCESS(status);
#elif _WIN32
    NTSTATUS status = BCryptGenRandom(NULL, buf, nbytes, BCRYPT_USE_SYSTEM_PREFERRED_RNG);
    return !BCRYPT_SUCCESS(status);
#else
    arc4random_buf(buf, nbytes);
    return 0;
#endif
}
