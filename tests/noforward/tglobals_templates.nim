discard """
  matrix: "--experimental:noForwardDecls"
  output: '''
(2, 1)
'''
"""
# a template or a macro's `quote` that refers to a global of its module is
# not hoisted over the global's declaration, it binds it like without
# noForwardDecls
import mglobals_templates

hit()
hit()
render(1)
echo totals()
