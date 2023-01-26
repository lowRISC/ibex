#include <stdint.h>

#include "semihosting.h"

size_t strlen(const char *buf)
{
    int len = 0;
    while (buf[len])
        len++;
    return len;
}

#define O_RDONLY         0
#define O_WRONLY         1
#define O_RDWR           2
#define O_RDWR           2
#define O_TRUNC		0x0800

int errno;

/* These semihosting functions came from the Freedom Metal source. */
static int open(const char *name, int flags, int mode) {
    int semiflags = 0;

    switch (flags & (O_RDONLY | O_WRONLY | O_RDWR)) {
    case O_RDONLY:
        semiflags = 0; /* 'r' */
        break;
    case O_WRONLY:
        if (flags & O_TRUNC)
            semiflags = 4; /* 'w' */
        else
            semiflags = 8; /* 'a' */
        break;
    default:
        if (flags & O_TRUNC)
            semiflags = 6; /* 'w+' */
        else
            semiflags = 10; /* 'a+' */
        break;
    }

    volatile semihostparam_t arg = {.param1 = (uintptr_t)name,
                                    .param2 = (uintptr_t)semiflags,
                                    .param3 = (uintptr_t)strlen(name)};

    int ret = (int)semihost_call_host(SEMIHOST_SYS_OPEN, (uintptr_t)&arg);
    if (ret == -1)
        errno = semihost_call_host(SEMIHOST_SYS_ERRNO, 0);
    return ret;
}

static ssize_t write(int file, const void *ptr, size_t len)
{
    volatile semihostparam_t arg = {.param1 = (uintptr_t)file,
                                    .param2 = (uintptr_t)ptr,
                                    .param3 = (uintptr_t)len};
    ssize_t ret =
        (ssize_t)semihost_call_host(SEMIHOST_SYS_WRITE, (uintptr_t)&arg);

    return (len - ret);
}

int main()
{
    char *filename = NULL;
    const char *message = "Hello, world!\n";
    const char *message2 = "Do re mi fa so la ti do!\n";
    int fd;

begin:
    fd = open(filename, O_WRONLY, 0644);
    write(fd, message, strlen(message));
    write(1, message2, strlen(message2));

    return 10;
}
