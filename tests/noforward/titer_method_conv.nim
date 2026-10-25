discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
3
2
1
woof rex
1.5 conv:2.0
20
'''
"""
# iterators, methods, converters, old style forward decls
for x in countDown3(): echo x
iterator countDown3(): int =
  var i = helper()
  while i > 0:
    yield i
    dec i
proc helper(): int = 3

method speak(a: Animal): string {.base.} = "..."
method speak(d: Dog): string = "woof " & name(d)
proc name(d: Dog): string = d.n
type
  Animal = ref object of RootObj
  Dog = ref object of Animal
    n: string
let a: Animal = Dog(n: "rex")
echo speak(a)

proc takesFloat(f: float): string = $f & useConv()
proc useConv(): string =
  let m = Meters(2)
  takesFloatOnly(m)
converter toFloat(m: Meters): float = m.float
proc takesFloatOnly(f: float): string = " conv:" & $f
type Meters = distinct int
echo takesFloat(1.5)

proc fwd(x: int): int
echo fwd(2)
proc fwd(x: int): int = x * 10
