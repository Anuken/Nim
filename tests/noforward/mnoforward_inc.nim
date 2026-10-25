proc fromInclude(): int = 42
proc useInc(): int = fromInclude() + helperAfter()
proc helperAfter(): int = 1
