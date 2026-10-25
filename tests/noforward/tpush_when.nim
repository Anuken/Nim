discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
-119 2
'''
"""
# push/pop and when
{.push overflowChecks: off.}
proc wrap(x: int8): int8 = x + bigger()
{.pop.}
proc bigger(): int8 = 127
when defined(nimHasNothing):
  proc onlyWhen(): int = 1
else:
  proc onlyWhen(): int = callLater()
proc callLater(): int = 2
echo wrap(10), " ", onlyWhen()
