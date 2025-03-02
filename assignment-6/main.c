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
extern SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2);
extern uint64_t *STACK_BOTTOM asm("STACK_BOTTOM");

uint64_t *HEAP;

const SNAKEVAL BOOL_TAG = 0x0000000000000001;
const SNAKEVAL BOOL_TRUE = 0xFFFFFFFFFFFFFFFF;
const SNAKEVAL BOOL_FALSE = 0x7FFFFFFFFFFFFFFF;
const SNAKEVAL NIL = 0x0000000000000001;

char *decode(SNAKEVAL val);
char *decode_tuple(SNAKEVAL *val);
SNAKEVAL tuple_equals(SNAKEVAL *val1, SNAKEVAL *val2);

char *decode(SNAKEVAL val)
{
  // Number
  if ((val & BOOL_TAG) == 0)
  {
    // printf("==================number==================\n");
    char *str_buffer = (char *)malloc(100 * sizeof(char)); // val is even ==> number
    sprintf(str_buffer, "%ld", ((int64_t)(val)) / 2);      // shift bits right to remove tag
    // printf("val is at address: %p\n", str_buffer);
    return str_buffer;
  }
  // True
  else if (val == BOOL_TRUE)
  {
    // printf("==================true==================\n");
    char *str_buffer = (char *)malloc(5 * sizeof(char));
    sprintf(str_buffer, "true");
    return str_buffer;
  }
  // False
  else if (val == BOOL_FALSE)
  {
    // printf("==================false==================\n");
    char *str_buffer = (char *)malloc(6 * sizeof(char));
    sprintf(str_buffer, "false");
    return str_buffer;
  }
  // Nil
  else if (val == NIL)
  {
    // printf("==================nil==================\n");
    char *str_buffer = (char *)malloc(4 * sizeof(char));
    sprintf(str_buffer, "nil");
    return str_buffer;
  }
  // Tuple (the only thing left that could end in a 1 at this point)
  else if ((val & BOOL_TAG) == 1)
  {
    // printf("==================tuple==================\n");
    // printf("==================tuple NEXT==================\n");
    uint64_t *ptr_of_val = (uint64_t *)(val ^ 0x1);
    // printf("==================tuple AFTER==================\n");
    return decode_tuple(ptr_of_val);
    // printf("==================END tuple==================\n");
  }
  // BAD VALUE
  else
  {
    // printf("==================unknown val==================\n");
    char *str_buffer = (char *)malloc(65 * sizeof(char));
    sprintf(str_buffer, "Unknown value: %#018lx\n", val); // print unknown val in hex
    return str_buffer;
  }
}

char *decode_tuple(SNAKEVAL *val)
{
  {
    int64_t length = val[0];
    // Empty tuple
    if (length == 0)
    {
      return strdup("()");
    }

    // Single
    else if (length == 1)
    {
      // char *item = decode(val);

      // I think this needs to be the following line,
      // rather than what it was before (above) because that would just
      // cycle us back to this function, right? The whole val is a tuple,
      // which we're decoding here. So we need to decode the pieces
      char *item = decode(val[1]);
      char *str_buffer = (char *)malloc((4 + strlen(item)) * sizeof(char));
      sprintf(str_buffer, "(%s,)", item);
      free(item);
      return str_buffer;
    }

    // >1-tuple
    else
    {
      char *result = strdup("(");
      size_t size = strlen(result) * sizeof(char);

      for (int i = 1; i <= length; i += 1)
      {
        char *decoded = decode(val[i]);
        size_t decoded_size = (5 + strlen(decoded) + strlen(result)) * sizeof(char);
        size = decoded_size;
        char *new_result = malloc(size);
        if (i == 1){
          sprintf(new_result, "%s%s", result, decoded); 
        } else if (i == length) {
          sprintf(new_result, "%s, %s)", result, decoded);
        } else {
          sprintf(new_result, "%s, %s", result, decoded);
        }
        free(result);
        free(decoded);
        result = new_result;
      }
      return result;
    }
  }
}

void printHelp(FILE *out, SNAKEVAL val)
{
  char *str = decode(val);
  fprintf(out, "%s", str);
  free(str);
}

SNAKEVAL print(SNAKEVAL val)
{

  printHelp(stdout, val);
  fprintf(stdout, "\n");
  fflush(stdout);
  return val;
}

char *decode_error(uint64_t code)
{
  int max_size = 60;

  char *str_buffer = malloc(max_size * sizeof(char));

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
    sprintf(str_buffer, "integer overflow! Got: ");
  }
  else if (code == 6)
  {
    sprintf(str_buffer, "expected a tuple, got: ");
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

void errorHelp(FILE *out, uint64_t code, SNAKEVAL bad_val)
{
  char *error_text = decode_error(code);
  char *bad_val_text = decode(bad_val);

  fprintf(out, "%s", error_text);
  free(error_text);

  fprintf(out, "%s", bad_val_text);
  free(bad_val_text);
}

void error(uint64_t code, SNAKEVAL bad_val)
{
  errorHelp(stderr, code, bad_val);
  fprintf(stderr, "\n");
  fflush(stderr);
  exit(code);
}

SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2)
{
  // Atomic types
  if ((val1 & BOOL_TAG) == 0 || (val1 == BOOL_TRUE) || (val1 == BOOL_FALSE) || (val1 == NIL))
  {
    // These will be just basic `uint64_t`s, so == is appropriate
    printf("Val1: %p, Val2: %p: ", val1, val2);
    if (val1 == val2)
    {
      printf("true\n");
      return BOOL_TRUE;
    }
    else
    {
      printf("false\n");
      return BOOL_FALSE;
    }
  }
  // Tuple (the only thing left that could end in a 1 at this point)
  else if ((val1 & BOOL_TAG) == 1 && (val2 & BOOL_TAG) == 1)
  {
    uint64_t *ptr_of_val1 = (uint64_t *)(val1 ^ 0x1);
    uint64_t *ptr_of_val2 = (uint64_t *)(val2 ^ 0x1);
    return tuple_equals(ptr_of_val1, ptr_of_val2);
  }
  else
  {
    return BOOL_FALSE;
  }
}

SNAKEVAL tuple_equals(SNAKEVAL *val1, SNAKEVAL *val2)
{
  int64_t size1 = val1[0];
  int64_t size2 = val2[0];

  if (size1 != size2)
  {
    return BOOL_FALSE;
  }

  for (int i = 1; i <= size1; i += 1)
  {
    char *cur_item_1 = decode(val1[i]);
    char *cur_item_2 = decode(val2[i]);

    if (strcmp(cur_item_1, cur_item_2) != 0)
    {
      return BOOL_FALSE;
    }
  }

  return BOOL_TRUE;
}

SNAKEVAL input()
{
  while (1)
  {
    // Amanda and Maya helped us learn about how to take user input in C.
    char *read = NULL;
    size_t min_size = 4;
    getline(&read, &min_size, stdin);

    if (strcmp(read, "true") == 0)
    {
      return BOOL_TRUE;
    }
    else if (strcmp(read, "false") == 0)
    {
      return BOOL_FALSE;
    }
    else if (strcmp(read, "nil") == 0)
    {
      return NIL;
    }
    else
    // Number case
    {
      // https://www.tutorialspoint.com/c_standard_library/c_function_strtoul.htm
      char *endptr;
      int64_t num = strtoul(read, &endptr, 10);

      if (num > 4611686018427387903 || num < -4611686018427387904)
      {
        printf("Invalid input: integer overflow!\n");
      }
      else if (endptr == read)
      {
        printf("Invalid input: must be a number, boolean, or `nil`.\n");
      }
      else {
        return num << 1;
      }
    }
  }
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
