#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(uint64_t val) asm("print");

uint64_t print(uint64_t val) {
  printf("Unknown value: %#018x\n", val);
  return val;
}

int main(int argc, char** argv) {
  uint64_t result = our_code_starts_here();
  print(result);
  return 0;
}
