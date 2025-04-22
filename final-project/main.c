#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "gc.h"
#include <setjmp.h>
// #include "except.h"

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t *HEAP, uint64_t size) asm("ocsh_0");
extern void error() asm("?error");
extern SNAKEVAL set_stack_bottom(uint64_t *stack_bottom) asm("?set_stack_bottom");
extern SNAKEVAL print(SNAKEVAL val) asm("?print");
extern SNAKEVAL input() asm("?input");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t *rsp, uint64_t *rbp, uint64_t args) asm("?print_stack");
extern SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2) asm("?equal");
extern uint64_t *try_gc(uint64_t *alloc_ptr, uint64_t amount_needed, uint64_t *first_frame, uint64_t *stack_top) asm("?try_gc");
extern uint64_t *HEAP_END asm("?HEAP_END");
extern uint64_t *HEAP asm("?HEAP");
extern void ex_raise() asm("?ex_raise");

const uint64_t NUM_TAG_MASK = 0x0000000000000001;
const uint64_t BOOL_TAG_MASK = 0x0000000000000007;
const uint64_t TUPLE_TAG_MASK = 0x0000000000000007;
const uint64_t CLOSURE_TAG_MASK = 0x0000000000000007;
const uint64_t FWD_PTR_TAG_MASK = 0x0000000000000007;
const uint64_t NUM_TAG = 0x0000000000000000;
const uint64_t BOOL_TAG = 0x0000000000000007;
const uint64_t TUPLE_TAG = 0x0000000000000001;
const uint64_t CLOSURE_TAG = 0x0000000000000005;
const uint64_t FWD_PTR_TAG = 0x0000000000000003;
const uint64_t BOOL_TRUE = 0xFFFFFFFFFFFFFFFF;
const uint64_t BOOL_FALSE = 0x7FFFFFFFFFFFFFFF;
const uint64_t RUNTIME_EXCEPTION = 0x3FFFFFFFFFFFFFFF;
const uint64_t VALUE_EXCEPTION = 0x1FFFFFFFFFFFFFFF;
const uint64_t NIL = ((uint64_t)NULL | TUPLE_TAG);

const uint64_t ERR_COMP_NOT_NUM = 1;
const uint64_t ERR_ARITH_NOT_NUM = 2;
const uint64_t ERR_LOGIC_NOT_BOOL = 3;
const uint64_t ERR_IF_NOT_BOOL = 4;
const uint64_t ERR_OVERFLOW = 5;
const uint64_t ERR_GET_NOT_TUPLE = 6;
const uint64_t ERR_GET_LOW_INDEX = 7;
const uint64_t ERR_GET_HIGH_INDEX = 8;
const uint64_t ERR_NIL_DEREF = 9;
const uint64_t ERR_OUT_OF_MEMORY = 10;
const uint64_t ERR_SET_NOT_TUPLE = 11;
const uint64_t ERR_SET_LOW_INDEX = 12;
const uint64_t ERR_SET_HIGH_INDEX = 13;
const uint64_t ERR_CALL_NOT_CLOSURE = 14;
const uint64_t ERR_CALL_ARITY_ERR = 15;
const uint64_t ERR_CRASH = 99;

size_t HEAP_SIZE;
uint64_t *STACK_BOTTOM;
uint64_t *HEAP;
uint64_t *HEAP_END;

SNAKEVAL set_stack_bottom(uint64_t *stack_bottom)
{
  STACK_BOTTOM = stack_bottom;
  return 0;
}

uint64_t *FROM_S;
uint64_t *FROM_E;
uint64_t *TO_S;
uint64_t *TO_E;

SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2)
{
  if (val1 == val2)
  {
    return BOOL_TRUE;
  }
  if (val1 == NIL || val2 == NIL)
  {
    return BOOL_FALSE;
  }
  if ((val1 & TUPLE_TAG_MASK) == TUPLE_TAG && (val2 & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    uint64_t *tup1 = (uint64_t *)(val1 - TUPLE_TAG);
    uint64_t *tup2 = (uint64_t *)(val2 - TUPLE_TAG);
    if (tup1[0] != tup2[0])
    {
      return BOOL_FALSE;
    }
    // we / 2, since tup1[0] is a SNAKEVAL!
    for (uint64_t i = 1; i <= tup1[0] / 2; i++)
    {
      if (equal(tup1[i], tup2[i]) == BOOL_FALSE)
        return BOOL_FALSE;
    }
    return BOOL_TRUE;
  }
  return BOOL_FALSE;
}

uint64_t tupleCounter = 0;
void printHelp(FILE *out, SNAKEVAL val)
{
  if (val == NIL)
  {
    fprintf(out, "nil");
  }
  else if ((val & NUM_TAG_MASK) == NUM_TAG)
  {
    fprintf(out, "%ld", ((int64_t)val) >> 1); // deliberately int64, so that it's signed
  }
  else if (val == BOOL_TRUE)
  {
    fprintf(out, "true");
  }
  else if (val == BOOL_FALSE)
  {
    fprintf(out, "false");
  }
  else if (val == RUNTIME_EXCEPTION)
  {
    fprintf(out, "RuntimeException");
  }
  else if (val == VALUE_EXCEPTION)
  {
    fprintf(out, "ValueException");
  }
  else if ((val & CLOSURE_TAG_MASK) == CLOSURE_TAG)
  {
    uint64_t *addr = (uint64_t *)(val - CLOSURE_TAG);
    fprintf(out, "[%p - 5] ==> <function arity %ld, closed %ld, fn-ptr %p>",
            (uint64_t *)val, addr[0] / 2, addr[1] / 2, (uint64_t *)addr[2]);
    // some of this commented-out code may be useful for debugging purposes

    /* fprintf(out, "\nClosed-over values:\n"); */
    /* for (uint64_t i = 0; i < addr[1] / 2; i++) { */
    /*   if (i > 0) { fprintf(out, "\n"); } */
    /*   if ((addr[3 + i] & TUPLE_TAG_MASK) == 5) { */
    /*     fprintf(out, "<closure %p>", (uint64_t*)addr[3 + i]); */
    /*   } else { */
    /*     printHelp(out, addr[3 + i]); */
    /*   } */
    /* } */
  }
  /* else if ((val & FWD_PTR_TAG_MASK) == FWD_PTR_TAG) { */
  /*   fprintf(out, "forwarding to "); */
  /*   fflush(out); */
  /*   fprintf(out, "%p", (int*)(val - FWD_PTR_TAG)); */
  /*   fflush(out); */
  /*   return; */
  /* } */
  else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    uint64_t *addr = (uint64_t *)(val - TUPLE_TAG);
    // Check whether we've visited this tuple already
    if ((*addr & 0x8000000000000000) != 0)
    {
      fprintf(out, "<cyclic tuple %d>", (int)(*addr & 0x7FFFFFFFFFFFFFFF));
      return;
    }
    /* if (!(addr >= FROM_S && addr < FROM_E) && !(addr >= TO_S && addr < TO_E)) { */
    /*   fprintf(out, "DANGLING POINTER %p", addr); */
    /*   return; */
    /* } */
    // Mark this tuple: save its length locally, then mark it

    // by storing as a SNAKEVAL, we buy ourselves one bit!
    uint64_t len = addr[0];
    if (len & NUM_TAG_MASK)
    { // actually, it's a forwarding pointer
      fprintf(out, "forwarding to %p", (uint64_t *)(len - 1));
      return;
    }
    else
    {
      len /= 2; // length is encoded as SNAKEVAL
    }
    /* fprintf(out, "Heap is:\n"); */
    /* naive_print_heap(HEAP, HEAP_END); */
    /* fprintf(out, "%p-->(len=%d)", (int*)(val - 1), len / 2); */
    /* fflush(out); */
    *(addr) = 0x8000000000000000 | (++tupleCounter);
    fprintf(out, "(");
    for (uint64_t i = 1; i <= len; i++)
    {
      if (i > 1)
        fprintf(out, ", ");
      printHelp(out, addr[i]);
    }
    if (len == 1)
      fprintf(out, ", ");
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len * 2; // length is encoded
  }
  else
  {
    fprintf(out, "Unknown value: %#018lx", val);
  }
}

SNAKEVAL printStack(SNAKEVAL val, uint64_t *rsp, uint64_t *rbp, uint64_t args)
{
  printf("RSP: %#018lx\t==>  ", (uint64_t)rsp);
  fflush(stdout);
  printHelp(stdout, *rsp);
  fflush(stdout);
  printf("\nRBP: %#018lx\t==>  ", (uint64_t)rbp);
  fflush(stdout);
  printHelp(stdout, *rbp);
  fflush(stdout);
  printf("\n(difference: %ld)\n", (uint64_t)(rsp - rbp));
  fflush(stdout);
  printf("Requested return val: %#018lx\t==> ", (uint64_t)val);
  fflush(stdout);
  printHelp(stdout, val);
  fflush(stdout);
  printf("\n");
  fflush(stdout);
  printf("Num args: %ld\n", args);

  uint64_t *origRsp = rsp;

  if (rsp > rbp)
  {
    printf("Error: RSP and RBP are not properly oriented\n");
    fflush(stdout);
  }
  else
  {
    for (uint64_t *cur = rsp; cur < STACK_BOTTOM + 3; cur++)
    {
      if (cur == STACK_BOTTOM)
      {
        printf("BOT %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur);
        fflush(stdout);
      }
      else if (cur == rbp)
      {
        printf("RBP %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur);
        fflush(stdout);
      }
      else if (cur == origRsp)
      {
        printf("    %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur);
        fflush(stdout);
      }
      else if (cur == rbp + 1)
      {
        printf("    %#018lx: %#018lx\t==>  saved ret\n", (uint64_t)cur, *cur);
        fflush(stdout);
        rsp = rbp + 2;
        rbp = (uint64_t *)(*rbp);
      }
      else if (cur == STACK_BOTTOM + 2)
      {
        printf("    %#018lx: %#018lx\t==>  heap\n", (uint64_t)cur, *cur);
        fflush(stdout);
      }
      else
      {
        printf("    %#018lx: %#018lx\t==>  ", (uint64_t)cur, *cur);
        fflush(stdout);
        printHelp(stdout, *cur);
        fflush(stdout);
        printf("\n");
        fflush(stdout);
      }
    }
  }
  return val;
}

SNAKEVAL input()
{
  uint64_t ans;
  scanf("%ld", &ans);
  return ans << 1;
}

SNAKEVAL print(SNAKEVAL val)
{
  printHelp(stdout, val);
  printf("\n");
  fflush(stdout);
  return val;
}

void error(uint64_t code, SNAKEVAL val)
{
  switch (code)
  {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number, got ");
    printHelp(stderr, val);
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number, got ");
    printHelp(stderr, val);
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error: logic expected a boolean, got ");
    printHelp(stderr, val);
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean, got ");
    printHelp(stderr, val);
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: Integer overflow, got ");
    printHelp(stderr, val);
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple, got ");
    printHelp(stderr, val);
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to get, got %ld\n", (uint64_t)val);
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to get, got %ld\n", (uint64_t)val);
    break;
  case ERR_NIL_DEREF:
    fprintf(stderr, "Error: tried to access component of nil\n");
    break;
  case ERR_OUT_OF_MEMORY:
    fprintf(stderr, "Error: out of memory\n");
    break;
  case ERR_SET_NOT_TUPLE:
    fprintf(stderr, "Error: set expected tuple\n");
    break;
  case ERR_SET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to set\n");
    break;
  case ERR_SET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to set\n");
    break;
  case ERR_CALL_NOT_CLOSURE:
    fprintf(stderr, "Error: tried to call a non-closure value: ");
    printHelp(stderr, val);
    break;
  case ERR_CALL_ARITY_ERR:
    fprintf(stderr, "Error: arity mismatch in call\n");
    break;
  case ERR_CRASH:
    fprintf(stderr, "Error: CRASH\n");
    break;
  default:
    fprintf(stderr, "Error: Unknown error code: %ld, val: ", code);
    printHelp(stderr, val);
  }
  fprintf(stderr, "\n%p ==> ", (uint64_t *)val);
  printHelp(stderr, val);
  fprintf(stderr, "\n");
  fflush(stderr);
  naive_print_heap(stderr, HEAP, HEAP_END);
  fflush(stdout);
  free(HEAP);
  exit(code);
}

/*
  Try to reserve the desired number of bytes of memory, and free garbage if
  needed.  Fail (and exit the program) if there is insufficient memory.  Does
  not actually allocate the desired number of bytes of memory; the caller
  will do that.

  Arguments:

    uint64_t* alloc_ptr - the current top of the heap (which we store in R15), where
                          the next allocation should occur, if possible
    uint64_t bytes_needed - the number of bytes of memory we want to allocate
                            (including padding)
    uint64_t* cur_frame - the base pointer of the topmost stack frame of our code
                          (i.e., RBP)
    uint64_t* cur_stack_top - the stack pointer of the topmost stack frame of our
                              code (i.e., RSP)

  Returns:
    The new top of the heap (i.e. the new value of R15) after garbage collection.
    Does not actually allocate bytes_needed space.

  Side effect:
    Also updates HEAP and HEAP_END to point to the new location of the heap
*/
uint64_t *try_gc(uint64_t *alloc_ptr, uint64_t bytes_needed, uint64_t *cur_frame, uint64_t *cur_stack_top)
{
  uint64_t *new_heap = (uint64_t *)calloc(HEAP_SIZE + 15, sizeof(uint64_t));
  uint64_t *old_heap = HEAP;
  uint64_t *old_heap_end = HEAP_END;

  uint64_t *new_r15 = (uint64_t *)(((uint64_t)new_heap + 15) & ~0xF);
  uint64_t *new_heap_end = new_r15 + HEAP_SIZE;

  FROM_S = (uint64_t *)(((uint64_t)HEAP + 15) & ~0xF);
  FROM_E = HEAP_END;
  TO_S = new_r15;
  TO_E = new_heap_end;

  /* printf("FROM_S = %p, FROM_E = %p, TO_S = %p, TO_E = %p\n", FROM_S, FROM_E, TO_S, TO_E); */
  /* naive_print_heap(FROM_S, FROM_E); */
  /* printStack(BOOL_TRUE, cur_stack_top, cur_frame, 0); */

  // Abort early, if we can't allocate a new to-space
  if (new_heap == NULL)
  {
    fprintf(stderr, "Out of memory: could not allocate a new semispace for garbage collection\n");
    fflush(stderr);
    if (old_heap != NULL)
      free(old_heap);
    exit(ERR_OUT_OF_MEMORY);
  }

  new_r15 = gc(STACK_BOTTOM, cur_frame, cur_stack_top, FROM_S, HEAP_END, new_r15);
  HEAP = new_heap;
  HEAP_END = new_heap_end;
  free(old_heap);

  // Note: strict greater-than is correct here: if new_r15 + (bytes_needed / 8) == HEAP_END,
  // that does not mean we're *using* the byte at HEAP_END, but rather that it would be the
  // next free byte, which is still ok and not a heap-overflow.
  if (bytes_needed / sizeof(uint64_t) > HEAP_SIZE)
  {
    fprintf(stderr, "Allocation error: needed %ld words, but the heap is only %ld words\n",
            bytes_needed / sizeof(uint64_t), HEAP_SIZE);
    fflush(stderr);
    if (new_heap != NULL)
      free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  }
  else if ((new_r15 + (bytes_needed / sizeof(uint64_t))) > HEAP_END)
  {
    fprintf(stderr, "Out of memory: needed %ld words, but only %ld remain after collection\n",
            bytes_needed / sizeof(uint64_t), (HEAP_END - new_r15));
    fflush(stderr);
    if (new_heap != NULL)
      free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  }
  else
  {
    /* fprintf(stderr, "new_r15 = %p\n", new_r15); */
    /* naive_print_heap(HEAP, HEAP_END); */
    return new_r15;
  }
}

// Exception stack entry
typedef struct ExStackEntry
{
  struct ExStackEntry *prev; // Link to previous entry
  jmp_buf context;           // Saved execution context
  SNAKEVAL exception_type;
  void *exception_data; // Storage for caught exception
} ExStackEntry;

// Global exception stack
ExStackEntry *global_exception_stack = NULL;

// Add an exception handler to the exception handler stack
void add_handler() {
  
}


// Raise an exception
void ex_raise(SNAKEVAL ex)
{
  ExStackEntry *entry = global_exception_stack;

  // Find a handler that can handle this exception
  while (entry != NULL)
  {
    if (entry->exception_type == ex)
    {
      // Save exception data for the handler
      entry->exception_data = ex;

      // Unwind the stack and jump to the handler
      global_exception_stack = entry->prev;
      longjmp(entry->context, ex);
    }
    entry = entry->prev;
  }

  // No handler found
  fprintf(stderr, "Unhandled exception: ");
  printHelp(stderr, ex);
  exit(1);
}

void setup_test() {
  // TODO: Add a handler for this test.
  exit(1);
}

SNAKEVAL call_snake(SNAKEVAL snake_closure) {
  if ((snake_closure & CLOSURE_TAG) != CLOSURE_TAG) {
    fprintf(stderr, "Invalid data in call_snake: %lld\n", snake_closure);
    printHelp(stderr, snake_closure);
    fprintf(stderr, "\n");
    return NIL;
  } else {
    
  }


}


// Raise an exception
void ex_raise_test(SNAKEVAL ex, uint64_t *return_addr)
{
  // No handler found
  fprintf(stderr, "Failure! Test raised exception: ");
  printHelp(stderr, ex);

}

int main(int argc, char **argv)
{
  // TODO: Make this bigger :3
  HEAP_SIZE = 1000;
  if (argc > 1)
  {
    HEAP_SIZE = atoi(argv[1]);
  }
  if (HEAP_SIZE < 0 || HEAP_SIZE > 1000000)
  {
    HEAP_SIZE = 0;
  }
  HEAP = (uint64_t *)calloc(HEAP_SIZE + 15, sizeof(uint64_t));

  uint64_t *aligned = (uint64_t *)(((uint64_t)HEAP + 15) & ~0xF);
  HEAP_END = aligned + HEAP_SIZE;
  /* printf("HEAP = %p, aligned = %p, HEAP_END = %p\n", HEAP, aligned, HEAP_END); */
  SNAKEVAL result = our_code_starts_here(aligned, HEAP_SIZE);
  // smarter_print_heap(aligned, HEAP_END, TO_S, TO_E);
  print(result);

  free(HEAP);
  return 0;
}