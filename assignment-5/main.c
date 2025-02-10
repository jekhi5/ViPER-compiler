#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here() asm("our_code_starts_here");
extern SNAKEVAL print(SNAKEVAL val) asm("print");

SNAKEVAL print(SNAKEVAL val) {
  // COPY YOUR IMPLEMENTATION FROM COBRA
  return val;
}

/*

COPY YOUR IMPLEMENTATION FROM COBRA

*/


// main should remain unchanged
int main(int argc, char** argv) {
  SNAKEVAL result = our_code_starts_here();
  print(result);
  return 0;
}
