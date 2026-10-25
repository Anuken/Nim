{.experimental: "dotOperators".}
type D* = distinct int
template `.`*(x: D, f: untyped): untyped = 42

proc g*[T](x: T): int =
  # `color` is declared after `g`: the dot operator still applies, and
  # `private` is bound although it is not exported
  result = x.color + private(1)

proc color(s: string): int = 1
proc private(x: int): int = x
