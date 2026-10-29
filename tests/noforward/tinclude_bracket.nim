discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
playing
3
'''
"""
# the types of `include a/[b, c]` files are hoisted like those of a plain include
type
  State = object
    menu: Menu = Menu.playing
    stats = Stats(count: 3)

var state = State()
echo state.menu
echo state.stats.count

include mbracket/[mmenu, mstats]
