#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t* HEAP, int size) asm("our_code_starts_here");
extern void error(uint64_t code, SNAKEVAL val) asm("error");
extern SNAKEVAL print(SNAKEVAL val) asm("print");
extern SNAKEVAL input() asm("input");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t* esp, uint64_t* ebp, int args) asm("print_stack");
extern uint64_t* STACK_BOTTOM asm("STACK_BOTTOM");

uint64_t* HEAP;


void printHelp(FILE *out, SNAKEVAL val) {
  // COPY YOUR IMPLEMENTATION FROM DIAMONDBACK
  // and enhance it to handle tuples
  return val;
}

SNAKEVAL print(SNAKEVAL val) {
  printHelp(stdout, val);
  printf("\n");
  fflush(stdout);
  return val;
}

/*

COPY YOUR IMPLEMENTATION FROM DIAMONDBACK

*/


// main should remain unchanged
// You can pass in a numeric argument to your program when you run it,
// to specify the size of the available heap.  You may find this useful
// for debugging...
int main(int argc, char** argv) {
  int size = 100000;
  if (argc > 1) { size = atoi(argv[1]); }
  if (size < 0 || size > 1000000) { size = 0; }
  HEAP = calloc(size, sizeof (int));

  SNAKEVAL result = our_code_starts_here(HEAP, size);
  print(result);
  free(HEAP);
  return 0;
}
