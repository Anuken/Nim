discard """
  output: "4 4"
"""

# a type symbol used in `quote` inside a for loop body over an iterator with
# several yields must keep its typedesc type after transf duplicates the loop
# body

import std/macros

type IdBaseType = int32

iterator twice(): int =
  yield 0
  yield 1

macro gen(): untyped =
  result = newStmtList()
  for i in twice():
    let name = ident("X" & $i)
    result.add quote do:
      type `name` = distinct `IdBaseType`

gen()
echo sizeof(X0), " ", sizeof(X1)
