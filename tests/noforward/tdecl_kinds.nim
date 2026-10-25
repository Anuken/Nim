discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
3 2 tagged
11
auto 5
'''
"""
# declarations that the types need, or that need what a macro produces
import std/macros

when defined(noforwardNotDefined):
  type Vec2[T] = object
    x, y: T
else:
  type Vec2[T] = array[2, T]

type IVec2 = Vec2[int32]           # a type of a `when defined` branch

const dir = "d"
{.pragma: tagged, deprecated: dir & "x".}  # a user pragma that a type uses
template tag {.pragma.}            # a custom pragma that a field uses

type Holder = object
  v: IVec2
  t {.tag.}: int

type Old {.tagged.} = object

macro makeType(name: untyped): untyped =
  result = quote do:
    type `name` = object
      x: int

makeType(Generated)

# a type section that needs the macro's type is checked after it:
type Wrapper = object
  g: Generated

proc getIt: auto = 5               # an `auto` return type of a deferred body

let h = Holder(v: [3'i32, 2], t: 1)
echo h.v[0], " ", h.v[1], " ", (if h.t.hasCustomPragma(tag): "tagged" else: "")
echo Wrapper(g: Generated(x: 11)).g.x
echo "auto ", getIt()
