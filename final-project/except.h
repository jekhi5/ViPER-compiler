#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <setjmp.h>

void ex_raise(uint64_t* ex) asm("?ex_raise");

void ex_return() asm("?ex_return");