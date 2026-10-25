discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
2 7
'''
"""
# enums that declare fields of the same name are not mutually dependent, and
# a type section waits for the types it uses, like an array index type
type Axis = enum
  leftX, leftY, leftTrigger, rightTrigger

type Button = enum
  a, b, leftTrigger, rightTrigger, unset

type Pad = object
  buttons: array[Button, bool]
  axes: array[Axis, float]
  name: string

proc name(p: Pad): string = p.name

var p = Pad(name: "x")
p.buttons[Button.leftTrigger] = true
echo ord(Button.leftTrigger), " ", sizeof(p.buttons) + name(p).len + 1
