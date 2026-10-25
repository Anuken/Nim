discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
async 42
'''
"""
import std/asyncdispatch
proc main() {.async.} =
  let v = await compute(2)
  echo "async ", v
proc compute(x: int): Future[int] {.async.} =
  await sleepAsync(1)
  return x * 21
waitFor main()
