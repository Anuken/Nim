discard """
  matrix: "--experimental:noForwardDecls --mm:arc; --experimental:noForwardDecls --mm:orc"
  output: '''
3 1
1 2
'''
"""
# a converter's body is checked when it is declared, so it is not hoisted
# over the globals of its module that it uses
import mconverter_globals

proc takesInt(x: int): int = x

echo takesInt(Wide("abc")), " ", counts()
echo takesInt(cstring"a"), " ", takesInt(cstring"b")

var later = 5
converter fromBool(b: bool): int = (if b: later else: 0)
doAssert takesInt(true) == 5
