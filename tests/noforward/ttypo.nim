discard """
  matrix: "--experimental:noForwardDecls"
  errormsg: "undeclared identifier: 'notDeclaredAnywhere'"
  line: 7
"""
# a typo must still be an error with a correct location
proc f(): int = notDeclaredAnywhere(3)
echo f()
