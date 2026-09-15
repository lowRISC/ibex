#include <sail_failure.h>

#include <stdio.h>
#include <stdlib.h>

void sail_match_failure(char *message)
{
     fprintf(stderr, "Match failure: %s\n", message);
#ifndef SAIL_NO_FAILURE
     exit(EXIT_FAILURE);
#endif
}

void sail_failure(char *message)
{
     fprintf(stderr, "Failure: %s\n", message);
#ifndef SAIL_NO_FAILURE
     exit(EXIT_FAILURE);
#endif
}

int sail_assert(bool result, char *message)
{
     if (~result) {
          fprintf(stderr, "Assert failed: %s\n", message);
#ifndef SAIL_NO_FAILURE
          exit(EXIT_FAILURE);
#endif
          return 0;
     }
     return 0;
}
