# `keyS` is ambiguous with the `keys` iterators from std/tables because of
# style insensitivity; outside of generics a field default resolves the sym
# choice like it did before 2.2 (first match, the enum field here)

import mfielddefault_ambiguous, std/tables

type
  Binds = object
    left = keyA
    down = keyS

doAssert Binds().down == keyS
discard initTable[int, int]()
