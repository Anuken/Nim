discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
3  -1
'''
"""
const N = 3
type
  Kind = enum kA, kB, kC
  Arr = array[N, int]

  FileIndex = distinct int32
  Info = object
    f: FileIndex
const

  Invalid = FileIndex(-1)
  info = Info(f: Invalid)
var a: Arr
echo a.len, " ", " ", info.f.int
