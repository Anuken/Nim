discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
[1, 2, 5, 10]
'''
"""
# VM: const evaluated through routines declared later
const table = buildTable()
proc buildTable(): array[4, int] =
  for i in 0..3: result[i] = sq(i)
proc sq(x: int): int = x * x + offset()
proc offset(): int = 1
static: echo "static ", sq(3)
echo table
