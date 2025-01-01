#include <stdint.h>

void ebreak()
{
    asm volatile("ebreak");
}

unsigned int fib(unsigned int n)
{
    if (n == 0) {
        return 0;
    }

    unsigned int a = 0;
    unsigned int b = 1;

    for (unsigned int i = 1; i < n; i++) {
        unsigned int next = a + b;
        a = b;
        b = next;
        ebreak();
    }

    return b;
}

int main()
{
begin:
    fib(4);
}
