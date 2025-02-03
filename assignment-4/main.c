#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(uint64_t val) asm("print");

const uint64_t BOOL_TAG   = 0x0000000000000001;
const uint64_t BOOL_TRUE  = 0xFFFFFFFFFFFFFFFF; 
const uint64_t BOOL_FALSE = 0x7FFFFFFFFFFFFFFF;

uint64_t print(uint64_t val) {

  // printf("\nVALUE: %lu", val);

  // Number
  if ((val & BOOL_TAG) == 0) { // val is even ==> number
    printf("%ld", ((int64_t)(val)) / 2); // shift bits right to remove tag
  // All else is boolean
  } else if (val == BOOL_TRUE) {
    printf("true");
  } else if (val == BOOL_FALSE) {
    printf("false");
  } else {
    // printf("BAD %ld\n", val);
    printf("Unknown value: %#018x", val); // print unknown val in hex
  }
  return val;
}

int main(int argc, char** argv) {
  uint64_t result = our_code_starts_here();
  print(result);
  return 0;
}
