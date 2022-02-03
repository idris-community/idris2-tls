#include <stdlib.h>

#if defined(_WIN32) || defined(_WIN64)
#define __WINDOWS__ 1
#endif

#ifdef __linux__
#include <sys/random.h>
#elif __WINDOWS__
#include <windows.h>
#include <bcrypt.h>
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
