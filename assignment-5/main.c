#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here() asm("our_code_starts_here");
extern SNAKEVAL print(SNAKEVAL val) asm("print");

SNAKEVAL print(SNAKEVAL val) {
  // Number
  if ((val & BOOL_TAG) == 0)
  {                                        // val is even ==> number
    printf("%ld\n", ((int64_t)(val)) / 2); // shift bits right to remove tag
    // All else is boolean
  }
  else if (val == BOOL_TRUE)
  {
    printf("true\n");
  }
  else if (val == BOOL_FALSE)
  {
    printf("false\n");
  }
  else
  {
    printf("Unknown value: %#018x", val); // print unknown val in hex
  }
  return val;
}

int64_t error(int64_t code, SNAKEVAL bad_val)
{
  if (code == 1)
  {
    fprintf(stderr, "comparison expected a number\n");
  }
  else if (code == 2)
  {
    fprintf(stderr, "arithmetic expected a number\n");
  }
  else if (code == 3)
  {
    fprintf(stderr, "logic expected a boolean\n");
  }
  else if (code == 4)
  {
    fprintf(stderr, "if expected a boolean\n");
  }
  else if (code == 5)
  {
    fprintf(stderr, "Integer overflow!\n");
  }
  else
  {
    fprintf(stderr, "Unknown error code");
  }
  exit(code);
}


// main should remain unchanged
int main(int argc, char** argv) {
  SNAKEVAL result = our_code_starts_here();
  print(result);
  return 0;
}
