#ifndef EXCEPT_H
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>

typedef long SNAKEVAL; // or whatever your tagged‐value type is

// One entry per nested try/catch
typedef struct ExStackEntry
{
  jmp_buf context;           // where to jump back on exn
  SNAKEVAL exception_type;   // which type this handler catches
  SNAKEVAL exception_data;   // the actual thrown value
  struct ExStackEntry *prev; // previous handler
} ExStackEntry;

// Top of the stack of active handlers
extern ExStackEntry *global_exception_stack;

// Provided by your compiler‐RT / generated stubs:
SNAKEVAL call0(void *clos);
SNAKEVAL call1(void *clos, SNAKEVAL arg);

// Push a new exception handler, run the try‐closure, then
// dispatch to catch‐closure on a matching exception.
SNAKEVAL try_catch(void *try_closure,
                   void *catch_closure,
                   SNAKEVAL exception_type);

// Raise an exception.  Searches global_exception_stack for the
// first handler whose exception_type matches, then longjmps to it.
void ex_raise(SNAKEVAL ex);

#endif