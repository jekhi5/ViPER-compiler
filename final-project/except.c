#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <setjmp.h>

typedef uint64_t SNAKEVAL;

// Thanks to Claude for the skeleton...

struct exception_handler {
    struct exception_handler *prev;     // Link to previous entry (outer try block)
    jmp_buf context;                    // Saved execution context (setjmp/longjmp)
    SNAKEVAL *exception_type;           // For which kind of exception is this handler looking? 
    void *exception_scratch;            // Space to store the current exception during handling
};

/* Global pointer to the top of the exception handler stack */
struct exception_handler *global_exception_stack = NULL;

void initialize_handler_stack() {
    // TODO... set the bottom of the handler stack
    global_exception_stack = NULL;
}

/*
 * ex_dispatcher - Main exception handling mechanism
 *
 * This function:
 * 1. Walks up the stack looking for handlers
 * 2. Unwinds the stack when a handler is found
 * 3. Transfers control to the appropriate handler
 *
 * Implementation varies based on the exception handling technique used:
 * - Threaded exception stack
 * - PC-based techniques (in-code markers, hash tables, range tables)
 */
void ex_dispatcher(SNAKEVAL* current_exception)
{
    // Get the top of the exception handler stack
    struct exception_handler *cur_handler = global_exception_stack;
    int match;

    // Walk the stack to find the first appropriate handler.
    while (cur_handler != NULL)
    {
        // Check if the current handler works.
        match = (*current_exception == *cur_handler->exception_type);
        if (match > 0)
        {
            // Handler found - update stack pointer and transfer control
            global_exception_stack = cur_handler->prev;
            cur_handler->exception_scratch = current_exception;
            longjmp(cur_handler->context, match);
            // Never returns
        }
        cur_handler = cur_handler->prev;
    }

    // No handler found
    fprintf(stderr, "Unhandled exception\n");
    print_exception_info(current_exception);
    abort();
}

/*
 * ex_raise - Pushes exception data onto the exception stack and transfers control
 * to the exception dispatcher.
 *
 * Parameters:
 *   ed - Exception data (the value being thrown)
 *   et - Exception type information
 *
 * This function does not return to the caller. Control is transferred to the
 * appropriate exception handler if one is found.
 */
void ex_raise(SNAKEVAL *ed, SNAKEVAL *et) {
    // Push exception data onto the exception data stack
    push_exception_data(ed, et);
    
    // Enter the exception dispatcher
    ex_dispatcher();
    
    // Should never reach here - dispatcher doesn't return
    abort();
}

/*
 * ex_reraise - Re-enters the exception dispatcher using the current exception.
 * 
 * This is used to implement re-throwing an exception after finalization code
 * is executed, or to implement a naked "throw;" statement in C++.
 * 
 * This function does not return to the caller. Control is transferred to the
 * next appropriate exception handler if one is found.
 */
void ex_reraise(void) {
    // Verify that there is an active exception
    if (exception_stack_empty()) {
        abort(); // No active exception to re-raise
    }
    
    // Enter the exception dispatcher with current stack top
    ex_dispatcher();
    
    // Should never reach here - dispatcher doesn't return
    abort();
}

/*
 * ex_return - Pops the topmost exception from the exception data stack.
 * 
 * This is called at the normal exit from an exception handler. It restores
 * the stack to the state it was in before the exception was raised.
 */
void ex_return(void) {
    // Verify that there is an active exception
    if (exception_stack_empty()) {
        abort(); // No active exception to pop
    }
    
    // Pop the exception data
    pop_exception_data();
    
    // Normal return - flow continues in the caller
}