#include <stdio.h>
#include <stdint.h>

extern int64_t our_code_starts_here() asm("our_code_starts_here");

int main(int argc, char** argv) {
  printf("%ld\n", our_code_starts_here());
  return 0;
}
