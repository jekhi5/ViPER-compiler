#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <setjmp.h>

typedef uint64_t SNAKEVAL;

// Thanks to Claude for the skeleton...

// Exception stack entry
typedef struct ExStackEntry {
    struct ExStackEntry* prev;   // Link to previous entry
    jmp_buf context;             // Saved execution context
    SNAKEVAL exception_type;
    void* exception_data;        // Storage for caught exception
} ExStackEntry;

// Global exception stack
ExStackEntry* global_exception_stack = NULL;

// Raise an exception
void ex_raise(SNAKEVAL* ex) {
    ExStackEntry* entry = global_exception_stack;
    
    // Find a handler that can handle this exception
    while (entry != NULL) {
        if (entry->exception_type == *ex ) {
            // Save exception data for the handler
            entry->exception_data = ex;
            
            // Unwind the stack and jump to the handler
            global_exception_stack = entry->prev;
            longjmp(entry->context, *ex);
        }
        entry = entry->prev;
    }
    
    // No handler found
    fprintf(stderr, "Unhandled exception (tag: %ld)\n", *ex);
    exit(1);
}

// Return from a handler (clean up)
void ex_return() {
    // Pop the exception stack
    if (global_exception_stack != NULL) {
        global_exception_stack = global_exception_stack->prev;
    }
}