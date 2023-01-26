#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

int main()
{
    int sum = 0;
    int counter = 0;

    while (counter < 10) {
        counter = counter + 1;
        sum = sum + counter;
    }

    return counter;
}
