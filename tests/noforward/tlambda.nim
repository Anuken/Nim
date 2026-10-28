discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
later 41
block 5 41
42
'''
"""
# the body of an anonymous routine in a top-level statement is deferred like
# the body of a top-level routine: it can use what is declared after it
type Entry = object
  setup: proc ()
  value: proc (): int

var entries: seq[Entry]
entries.add Entry(
  setup: (proc () = echo "later ", later()),
  value: (proc (): int = later() + 1))

block:
  let local = 5
  entries.add Entry(setup: (proc () = echo "block ", local, " ", later()),
    value: (proc (): int = 0))

proc later(): int = 41

for e in entries: e.setup()
echo entries[0].value()
