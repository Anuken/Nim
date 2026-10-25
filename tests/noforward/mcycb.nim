import mcyca {.cyclic.}
proc isOdd*(n: int): bool = n != 0 and isEven(n - 1)
proc newB*(x: int): B = B(x: x, a: nil)
proc bump*(): int = inc gcount; gcount
var gcount = 41
type B* = object
  x*: int
  a*: ref A
