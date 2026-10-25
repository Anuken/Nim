discard """
  matrix: "--experimental:noForwardDecls"
  output: "true B with 3 42"
"""
import mcyca, mcycb
echo isEven(10), " ", describe(newB(3))
