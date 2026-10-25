discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
ok
'''
"""
# effects inference across out-of-order mutual recursion
proc a(n: int) {.raises: [].} =
  if n > 0: b(n - 1)
proc b(n: int) =
  if n > 0: a(n - 1)
a(3)
echo "ok"
