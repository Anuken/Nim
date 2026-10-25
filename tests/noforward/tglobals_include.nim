discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
3
43
'''
"""
# globals and non-leading declarations
var counter = 0

proc bump() =
  inc counter
  later()

let threshold = 3

proc later() =
  if counter < threshold: bump()

bump()
echo counter
echo useInc()
include mnoforward_inc
