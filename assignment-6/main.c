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
const SNAKEVAL NIL = 0x0000000000000001;

char* decode(SNAKEVAL val);
char* decode_tuple(SNAKEVAL *val);


char* decode(SNAKEVAL val) {
  if ((val & BOOL_TAG) == 0)
  {            
    char* str_buffer = malloc(22 * sizeof(char)); // val is even ==> number
    sprintf(str_buffer, "%lld", ((int64_t)(val)) / 2); // shift bits right to remove tag
    return str_buffer;
  }
  else if (val == BOOL_TRUE)
  {
    char* str_buffer = malloc(5 * sizeof(char));
    sprintf(str_buffer, "true");
    return str_buffer;
  }
  else if (val == BOOL_FALSE)
  {
    char* str_buffer = malloc(6 * sizeof(char));
    sprintf(str_buffer, "false");
    return str_buffer;
  }
  else if (val == NIL) {
    char* str_buffer = malloc(3 * sizeof(char));
    sprintf(str_buffer, "nil");
    return str_buffer;
  }
  else if ((val & BOOL_TAG) == 1)
  {
    int64_t *ptr_of_val = (int64_t *) (val ^ 0x1);
    return decode_tuple(*ptr_of_val);
  }
  else
  {
    char* str_buffer = malloc(65 * sizeof(char));
    sprintf("Unknown value: %#018llx\n", val); // print unknown val in hex
    return str_buffer;
  }
}

char* decode_tuple(SNAKEVAL *val) {
  {
    int64_t length = val[0];
    // Empty tuple
    if (length == 0) {
      return strdup("()");
    } 
    
    // Single
    else if (length == 1)
    {
      char* item = decode(val);
      char* str_buffer = malloc((4 + strlen(item)) * sizeof(char));
      sprintf(str_buffer, "(%s,)", item);
      return str_buffer;
    } 

    // >1-tuple
    else 
    {
      int size = 2 * sizeof(char);
      char* result = malloc(size);
      sprintf(result, "(");

      for (int i = 1; i <= length; ++i) {
        char* decoded = decode(val[i]);
        strcat(result, decoded);
        free(decoded);
      }

      result = (char*)realloc(result, strlen(result) + 2);
      strcat(result, ")");

      return result;
    }
  }
}

void printHelp(FILE *out, SNAKEVAL val)
{
  char* str = decode(val);
  fprintf(out, str);
  free(str);
}

SNAKEVAL print(SNAKEVAL val)
{
  printHelp(stdout, val);
  printf("\n");
  fflush(stdout);
  return val;
}


char* decode_error(uint64_t code) {
  int max_size = 60;

  char* str_buffer = malloc(max_size * sizeof(char));

  if (code == 1)
  {
    sprintf(str_buffer, "comparison expected a number, got: ");
  }
  else if (code == 2)
  {
    sprintf(str_buffer, "arithmetic expected a number, got: ");
  }
  else if (code == 3)
  {
    sprintf(str_buffer, "logic expected a boolean, got: ");
  }
  else if (code == 4)
  {
    sprintf(str_buffer, "if expected a boolean, got: ");
  }
  else if (code == 5)
  {
    sprintf(str_buffer, "Integer overflow! Got: ");
  }
  else if (code == 6)
  {
    sprintf(str_buffer, "Expected a tuple, got: ");
  }
  else if (code == 7)
  {
    sprintf(str_buffer, "index out of range of tuple (index too small)! Got: ");
  }
  else if (code == 8)
  {
    sprintf(str_buffer, "index out of range of tuple (index too large)! Got: ");
  }
  else if (code == 9)
  {
    sprintf(str_buffer, "index expected a number, got: ");
  }
  else if (code == 10)
  {
    sprintf(str_buffer, "nil dereference error! Got: ");
  }
  else
  {
    sprintf(str_buffer, "Unknown error code.");
  }
  return str_buffer;
}


void errorHelp(FILE *out, uint64_t code, SNAKEVAL bad_val) {
  char* error_text = decode_error(code);
  char* bad_val_text = decode(bad_val);

  fprintf(out, error_text);
  free(error_text);

  fprintf(out, bad_val_text);
  free(bad_val_text);
}

void error(uint64_t code, SNAKEVAL bad_val)
{
  errorHelp(stderr, code, bad_val);
  printf("\n");
  fflush(stdout);
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
  HEAP = calloc(size, sizeof(int64_t));

  SNAKEVAL result = our_code_starts_here(HEAP, size);
  print(result);
  free(HEAP);
  return 0;
}
