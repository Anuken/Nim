discard """
  output: '''
1
-2
-1
-2
'''
"""

# lambdas inside the body of a for loop over an inline iterator with
# several yields are duplicated by transf; the copies must be owned by the
# copied outer lambda, otherwise lambda lifting fails with
# "environment misses"

iterator signs(): int =
  yield 1
  yield -1

var zzs: seq[proc(): int]

proc outer() =
  proc main() =
    for sign in signs():
      (proc(x: int) =
        zzs.add proc(): int = x)(sign)
      let f = proc(): int = sign * 2
      zzs.add f
  main()

outer()
for z in zzs: echo z()
