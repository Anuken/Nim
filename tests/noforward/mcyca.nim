import mcycb {.cyclic.}
proc isEven*(n: int): bool = n == 0 or isOdd(n - 1)
proc describe*(b: B): string = "B with " & $b.x & " " & helperA()
var counter = 0
proc helperA(): string = $bump()
type A* = object
  b*: ref B
