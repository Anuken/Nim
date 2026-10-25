import std/macros

var hits = 0
template hit*() = hits += 1

var counter = 0
macro useCounter(x: typed): untyped =
  result = quote do:
    counter += 1

proc render*[T](x: T) =
  useCounter(x)

proc totals*(): (int, int) = (hits, counter)
