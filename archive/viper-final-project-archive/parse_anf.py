#! /usr/bin/env python3
import re

INDENT_SIZE = 4

s = input("Enter ANF:")
s = re.sub(r'@\d+', '', s)
s = re.sub(r'(ctry|alet|aletrec)', r' \1', s)

words = s.split()

indentors = ('ctry', 'alet', 'aletrec')
dedentors = ('catch', 'in')

indent = 0
for word in words:
    if word in indentors:
        print(f'\n{" " * indent}{word}\n', end='')
        indent += INDENT_SIZE
        print(f'{" " * indent}', end='')
    elif word in dedentors:
        print(f'\n{" " * (indent - INDENT_SIZE)}{word}\n', end='')
        indent -= INDENT_SIZE
        print(f'{" " * indent}', end='')
    else:
        print(f'{word} ', end='')
print()