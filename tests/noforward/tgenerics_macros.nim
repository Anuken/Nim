discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
2 10 105
'''
"""
# templates/macros and generics calling later procs
import std/macros
template twice(x: untyped): untyped = (x) * 2

proc g[T](x: T): T = h(x)
proc h[T](x: T): T = x + 1

proc usesTpl(): int = twice(laterVal())
proc laterVal(): int = 5

macro mkProc(name: untyped): untyped =
  quote do:
    proc `name`(): int = laterVal() + 100

mkProc(generated)
echo g(1), " ", usesTpl(), " ", generated()
