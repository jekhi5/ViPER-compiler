#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(uint64_t val) asm("print");
extern int64_t error(int64_t code, uint64_t bad_val) asm("error");

const uint64_t BOOL_TAG = 0x0000000000000001;
const uint64_t BOOL_TRUE = 0xFFFFFFFFFFFFFFFF;
const uint64_t BOOL_FALSE = 0x7FFFFFFFFFFFFFFF;

// char decode_to_string(uint64_t val)[] {
//   if ((val & BOOL_TAG) == 0) {
//     return sprintf("%ld\n", ((int64_t)(val)) / 2);
//   } else if (val == BOOL_TRUE) {
//     return "true\n";
//   } else if (val == BOOL_FALSE) {
//     return "false\n";
//   } else {
//     return sprintf("%#018x\n", val); // print unknown val in hex
//   }
// }

uint64_t print(uint64_t val)
{

  // printf("\nVALUE: %lu", val);

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
    // printf("BAD %ld\n", val);
    printf("Unknown value: %#018x", val); // print unknown val in hex
  }
  return val;
}

int64_t error(int64_t code, uint64_t bad_val)
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

int main(int argc, char **argv)
{
  uint64_t result = our_code_starts_here();
  print(result);
  return 0;
}
