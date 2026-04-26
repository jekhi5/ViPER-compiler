#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here() asm("our_code_starts_here");
extern SNAKEVAL print(SNAKEVAL val) asm("print");

const SNAKEVAL BOOL_TAG = 0x0000000000000001;
const SNAKEVAL BOOL_TRUE = 0xFFFFFFFFFFFFFFFF;
const SNAKEVAL BOOL_FALSE = 0x7FFFFFFFFFFFFFFF;

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
    printf("Unknown value: %#018lx\n", val); // print unknown val in hex
  }
  return val;
}

int64_t error(int64_t code, SNAKEVAL bad_val)
{
  if (code == 1)
  {
    printf("comparison expected a number, got: ");
    print(bad_val);
  }
  else if (code == 2)
  {
    printf("arithmetic expected a number, got: ");
    print(bad_val);
  }
  else if (code == 3)
  {
    printf("logic expected a boolean, got: ");
    print(bad_val);
  }
  else if (code == 4)
  {
    printf("if expected a boolean, got: ");
    print(bad_val);
  }
  else if (code == 5)
  {
    printf("Integer overflow!, got: ");
    print(bad_val);
  }
  else
  {
    printf("Unknown error code.\n");
  }
  exit(code);
}


// main should remain unchanged
int main(int argc, char** argv) {
  SNAKEVAL result = our_code_starts_here();
  print(result);
  return 0;
}
