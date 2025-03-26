#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "gc.h"

typedef uint64_t SNAKEVAL;

void printHelp(FILE* out, SNAKEVAL val);
extern uint64_t NUM_TAG_MASK;
extern uint64_t CLOSURE_TAG_MASK;
extern uint64_t TUPLE_TAG_MASK;
extern uint64_t FWD_PTR_MASK;
extern uint64_t CLOSURE_TAG;
extern uint64_t TUPLE_TAG;
extern uint64_t FWD_PTR_TAG;
extern uint64_t NIL;
extern uint64_t tupleCounter;
extern uint64_t* STACK_BOTTOM;
extern uint64_t* FROM_S;
extern uint64_t* FROM_E;
extern uint64_t* TO_S;
extern uint64_t* TO_E;
extern uint64_t BOOL_TRUE;
extern uint64_t BOOL_FALSE;


void naive_print_heap(uint64_t* heap, uint64_t* heap_end) {
  printf("In naive_print_heap from %p to %p\n", heap, heap_end);
  for(uint64_t i = 0; i < (uint64_t)(heap_end - heap); i += 1) {
    printf("  %ld/%p: %p (%ld)\n", i, (heap + i), (uint64_t*)(*(heap + i)), *(heap + i));
  }
}

// Implement the functions below

void smarter_print_heap(uint64_t* from_start, uint64_t* from_end, uint64_t* to_start, uint64_t* to_end) {
  // Print out the entire heap (both semispaces), and
  // try to print values readably when possible

  // Attempt 1: naive print both semispaces:
  naive_print_heap(from_start, from_end);
  printf("\n======================\n");
  naive_print_heap(to_start, to_end);

  // // Attempt 2: try to print vlaues readably
  // printf("In naive_print_heap from %p to %p\n", from_start, from_end);
  // for(uint64_t i = 0; i < (uint64_t)(from_end - from_start); i += 1) {
  //   printf("  %ld/%p: %p (%ld)\n", i, (from_start + i), (uint64_t*)(*(from_start + i)), *(from_start + i));
  }
}

// If a value is primitive, it isn't stored on the heap.
int is_primitive(SNAKEVAL val) {
  return ((val & NUM_TAG_MASK == 0) || (val == NIL) || (val == BOOL_TRUE) || (val == BOOL_FALSE));
} 

int is_heap_allocated(SNAKEVAL val) {
  return !is_primitive(val);
}

/*
  Copies a Garter value from the given address to the new heap, 
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter value,
                     i.e. a tagged word.  
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location 
    with a forwarding pointer to its new location
 */
uint64_t* copy_if_needed(uint64_t* garter_val_addr, uint64_t* heap_top) {
  if (is_heap_allocated(*garter_val_addr)) {
    // 1. Get the size of the garter val.
    //    - If it is a tuple,    this is 1 + the first slot.
    //    - If it is a function, this is 3 + the value in the third slot.
    //    - In both cases, account for padding.
    uint64_t words;
    if ((*garter_val_addr & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
      words = ((uint64_t*) (*garter_val_addr - CLOSURE_TAG))[2] + 3;
    } else {
      words = ((uint64_t*) (*garter_val_addr - TUPLE_TAG))[0] + 1;
    }
    // Padding :)
    if (words % 2 > 0) {
      words += 1;
    }

    size_t garter_val_size = words * sizeof(uint64_t);

    // 2. Copy the value to heap_top.
    memcpy(heap_top, garter_val_addr, garter_val_size);

    // 3. Replace garter_val_addr with a pointer to heap_top.
    *garter_val_addr = heap_top;

    // 4. Increase heap_top by the necessary amount.
    heap_top = heap_top + garter_val_size;

    return heap_top;
  } else {
    // no-op for now
    return heap_top;
  }
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
    top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
uint64_t* gc(uint64_t* bottom_frame, uint64_t* top_frame, uint64_t* top_stack, uint64_t* from_start, uint64_t* from_end, uint64_t* to_start) {

  uint64_t* old_top_frame = top_frame;
  do {
    // CAREFULLY CONSIDER: do you need `top_stack + 1`?
    for (uint64_t* cur_word = top_stack; cur_word < top_frame; cur_word++) {
      to_start = copy_if_needed(cur_word, to_start);
    }
    /* Shift to next stack frame:
     * [top_frame] points to the saved RBP, which is the RBP of the next stack frame,
     * [top_frame + 8] is the return address, and
     * [top_frame + 16] is therefore the next frame's stack-top
     */
    top_stack = top_frame + 2;
    old_top_frame = top_frame;
    top_frame = (uint64_t*)(*top_frame);
  } while (old_top_frame <= bottom_frame); // Use the old stack frame to decide if there's more GC'ing to do
  // CAREFULLY CONSIDER: Should this be `<=` or `<`?

  // after copying and GC'ing all the stack frames, return the new allocation starting point
  return to_start;       
}

