discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
later 1
gen
2
4
'''
"""
# a module imported again after the first declarations (for example by an
# included file) cannot start a new import cycle: the declarations after it
# are still visible before it
import mreimport, std/[strutils {.all.}]
import mreimport {.all.} as mr
import mreimportdir/mnested {.all.} as mn
proc a() = later()
proc b() = generated()
import mreimport, std/[strutils {.all.}]
import mreimport {.all.} as mr
import mreimportdir/mnested {.all.} as mn
template gen(n: untyped) =
  template n*() = echo "gen"
proc later() = echo "later ", libValue()
gen(generated)
a()
b()
echo mr.hidden()
echo mn.nestedHidden()
