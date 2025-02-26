#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t *HEAP, int size) asm("our_code_starts_here");
extern void error(uint64_t code, SNAKEVAL val) asm("error");
extern SNAKEVAL print(SNAKEVAL val) asm("print");
extern SNAKEVAL input() asm("input");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t *esp, uint64_t *ebp, int args) asm("print_stack");
extern uint64_t *STACK_BOTTOM asm("STACK_BOTTOM");

uint64_t *HEAP;

const SNAKEVAL BOOL_TAG = 0x0000000000000001;
const SNAKEVAL BOOL_TRUE = 0xFFFFFFFFFFFFFFFF;
const SNAKEVAL BOOL_FALSE = 0x7FFFFFFFFFFFFFFF;

void printHelp(FILE *out, SNAKEVAL val)
{
  // Number
  if ((val & BOOL_TAG) == 0)
  {                                         // val is even ==> number
    printf("%lld\n", ((int64_t)(val)) / 2); // shift bits right to remove tag
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

  // TODO: print tuples and nil

  else
  {
    printf("Unknown value: %#018llx\n", val); // print unknown val in hex
  }
}

SNAKEVAL print(SNAKEVAL val)
{
  printHelp(stdout, val);
  printf("\n");
  fflush(stdout);
  return val;
}

void error(uint64_t code, SNAKEVAL bad_val)
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
    printf("Integer overflow! Got: ");
    print(bad_val);
  }
  else if (code == 6)
  {
    printf("Expected a tuple, got: ");
    print(bad_val);
  }
  else if (code == 7)
  {
    printf("Index out of range of tuple (index too small)! Got: ");
    print(bad_val);
  }
  else if (code == 8)
  {
    printf("Index out of range of tuple (index too large)! Got: ");
    print(bad_val);
  }
  else if (code == 9)
  {
    printf("Index expected a number, got: ");
    print(bad_val);
  }
  else if (code == 10)
  {
    printf("NIL dereference error! Got: ");
    print(bad_val);
  }
  else
  {
    printf("Unknown error code.\n");
  }
  exit(code);
}

// main should remain unchanged
// You can pass in a numeric argument to your program when you run it,
// to specify the size of the available heap.  You may find this useful
// for debugging...
int main(int argc, char **argv)
{
  int size = 100000;
  if (argc > 1)
  {
    size = atoi(argv[1]);
  }
  if (size < 0 || size > 1000000)
  {
    size = 0;
  }
  HEAP = calloc(size, sizeof(int));

  SNAKEVAL result = our_code_starts_here(HEAP, size);
  print(result);
  free(HEAP);
  return 0;
}
