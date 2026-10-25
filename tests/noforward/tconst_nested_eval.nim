discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
@[64, 128, 32]
8 xyabc
'''
"""
# a constant calls a routine whose deferred body is checked when the VM
# compiles it, and that check evaluates code itself (the `$instantiationInfo()`
# of `items`, `const k = g()`): the running code keeps its EOF and arguments
proc makeCodes(lengths: seq[uint8]): seq[uint16] =
  result = newSeq[uint16](lengths.len)
  var counts: array[16, uint8]
  for l in lengths:
    inc counts[l]
  for i in 0 ..< result.len:
    result[i] = uint16(counts[lengths[i]]) shl (lengths[i] - 2)

proc g(): int = 7
proc f(x: int): int =
  const k = g()
  result = x + k

proc h(): string = "abc"
proc s(x: string): string =
  const k = h()
  result = x & k

const codes = makeCodes(@[8'u8, 9, 7])
const a = f(1)
const b = s("xy")
echo codes
echo a, " ", b
