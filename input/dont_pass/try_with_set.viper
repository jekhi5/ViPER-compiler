# Attempts to increment the value at the given index
# Returns unchanged tuple if there's an error
def tup_inc(tup, index, amt):
  try tup[index] := tup[index] + amt catch RuntimeException as e in tup

tup_inc((1, 2, 3), 0, 2)