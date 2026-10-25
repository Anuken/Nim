discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
5
'''
"""
# macro generating a type; proc after it uses the type, proc before uses proc after
import std/macros
proc early(): int = useGen(Gen(v: 4))
macro genType(name: untyped): untyped =
  quote do:
    type `name` = object
      v: int
genType(Gen)
proc useGen(g: Gen): int = g.v + late()
proc late(): int = 1
echo early()
