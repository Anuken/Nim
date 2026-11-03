# like winim/winstr: a converter whose body uses globals declared before it
type Wide* = distinct string

var plainCount = 0

converter toLen*(x: Wide): int =
  inc plainCount
  string(x).len

when defined(gcDestructors):
  import std/deques
  var queue {.threadvar.}: Deque[string]
  var queueInit {.threadvar.}: bool

  proc keep(s: sink string): int =
    if not queueInit:
      queue = initDeque[string]()
      queueInit = true
    queue.addLast s
    queue.len

  converter toKept*(x: cstring): int = keep($x)

proc counts*(): int = plainCount
