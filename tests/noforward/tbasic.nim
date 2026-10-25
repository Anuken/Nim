discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
true P(1,2) kA
'''
"""
# basic: forward calls, mutual recursion, types used before declaration
proc main() =
  echo isEven(10), " ", describe(Point(x: 1, y: 2))

proc isEven(n: int): bool = n == 0 or isOdd(n - 1)
proc isOdd(n: int): bool = n != 0 and isEven(n - 1)

proc describe(p: Point): string = "P(" & $p.x & "," & $p.y & ") " & $p.kind

type Point = object
  x, y: int
  kind: Kind

type Kind = enum kA, kB

main()
