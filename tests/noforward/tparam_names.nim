discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
3
'''
"""
# the parameter names of a declaration are not dependencies on the routines
# of the module that have the same name: `effect` is declared before `color`
# and `pos`, so `item.color` stays a field access through the dot operator
{.experimental: "dotOperators".}
type Inst = distinct int
var store = @[(color: 3, pos: 0)]
template `.`(i: Inst, field: untyped): untyped = store[i.int].field

template effect(item: untyped, pos: int) =
  echo item.color

template pos(x: float, body: untyped): float = x
proc color(x: string): int = 1

proc run =
  effect(Inst(0), 0)
run()
