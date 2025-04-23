#include "except.h"
#include <stdint.h>
#include <setjmp.h>

extern void ex_raise() asm("?ex_raise");
extern SNAKEVAL try_catch(void *try_closure, void *catch_closure, SNAKEVAL exception_type) asm("?try_catch");

const uint64_t CLOSURE_TAG = 0x0000000000000005;

ExStackEntry *global_exception_stack = NULL;

// Zero‑arg closure call:
//   layout at raw = [ arity; code_ptr; num_free; ...free_vars ]
SNAKEVAL call0(void *clos)
{
    // 1) remove the low‑bit tag
    uintptr_t tagged = (uintptr_t)clos;
    uintptr_t raw = tagged & ~((uintptr_t)CLOSURE_TAG);

    // 2) treat raw as a pointer to words
    void **fields = (void **)raw;

    // 3) field[1] is the code pointer: fun0_t = SNAKEVAL (*)(void*)
    typedef SNAKEVAL (*fun0_t)(void *);
    fun0_t code_ptr = (fun0_t)fields[1];

    // 4) call it, passing its own env (fields)
    return code_ptr(fields);
}

// One‑arg closure call (for the catch‐block):
//   same layout, but code_ptr expects (env, arg)
SNAKEVAL call1(void *clos, SNAKEVAL arg)
{
    uintptr_t tagged = (uintptr_t)clos;
    uintptr_t raw = tagged & ~((uintptr_t)CLOSURE_TAG);
    void **fields = (void **)raw;

    typedef SNAKEVAL (*fun1_t)(void *, SNAKEVAL);
    fun1_t code_ptr = (fun1_t)fields[1];

    return code_ptr(fields, arg);
}

// Raise an exception `ex`.  Unwind until we find a handler
// whose .exception_type equals ex, then longjmp into it.
// If none match, crash.
void ex_raise(SNAKEVAL ex)
{
    ExStackEntry *entry = global_exception_stack;

    while (entry != NULL)
    {
        if (entry->exception_type == ex)
        {
            // stash the real exception payload
            entry->exception_data = ex;

            // pop this handler and jump into it
            global_exception_stack = entry->prev;
            longjmp(entry->context, 1);
            // (never returns)
        }
        entry = entry->prev;
    }

    // no matching handler
    fprintf(stderr, "Unhandled exception: ");
    printHelp(stderr, ex);
    exit(1);
}

// try_catch installs a new handler, runs `try_closure`, and if
// ex_raise is called with a matching type, will run `catch_closure`.
SNAKEVAL try_catch(void *try_closure,
                   void *catch_closure,
                   SNAKEVAL exception_type)
{
    ExStackEntry entry;

    // link into the global stack
    entry.prev = global_exception_stack;
    entry.exception_type = exception_type;
    entry.exception_data = 0;
    global_exception_stack = &entry;

    // save point: setjmp returns 0 initially, 1 on longjmp
    if (setjmp(entry.context) == 0)
    {
        // Normal path: invoke the try‐closure (0‐arg)
        SNAKEVAL result = call0(try_closure);

        // pop our handler and return the result
        global_exception_stack = entry.prev;
        return result;
    }
    else
    {
        // We got here via ex_raise → longjmp
        SNAKEVAL ex = entry.exception_data;

        // pop the handler (ex_raise already popped, but safe to do again)
        global_exception_stack = entry.prev;

        // invoke the catch‐closure with the exception value
        return call1(catch_closure, ex);
    }
}
