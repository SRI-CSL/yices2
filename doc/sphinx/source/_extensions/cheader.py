# -*- coding: utf-8 -*-
#
# The missing `c:header` directive for Sphinx's built-in C domain.
# This works similarly to the `py:module` directive.
#
# Written by Arto Bendiken <http://ar.to/>.
#
# This is free and unencumbered software released into the public domain.

from docutils import nodes
from docutils.parsers.rst import directives
from sphinx.util.compat import Directive
from sphinx import addnodes
from sphinx.locale import l_, _

class CHeaderDirective(Directive):
  has_content = False
  required_arguments = 1
  optional_arguments = 0
  final_argument_whitespace = False
  option_spec = {
    'synopsis': lambda text: text,
    'noindex': directives.flag,
    'deprecated': directives.flag,
  }

  def run(self):
    env = self.state.document.settings.env
    header_name = self.arguments[0].strip()
    option_noindex = 'noindex' in self.options
    env.temp_data['c:header'] = header_name

    result_nodes = []
    if not option_noindex:
      if not hasattr(env.domaindata['c'], 'headers'):
        env.domaindata['c']['headers'] = {}
      env.domaindata['c']['headers'][header_name] = \
        (env.docname, self.options.get('synopsis', ''), 'deprecated' in self.options)
      env.domaindata['c']['objects'][header_name] = (env.docname, u'header')

      target_id = nodes.make_id(header_name)
      target_node = nodes.target('', '', ids=[target_id], ismod=True)
      self.state.document.note_explicit_target(target_node)
      result_nodes.append(target_node)

      index_text = _('%s (C header)') % header_name
      index_node = addnodes.index(entries=[('single', index_text, target_id, '')])
      result_nodes.append(index_node)
    return result_nodes

def setup(app):
  app.require_sphinx('1.0')
  app.add_directive_to_domain('c', 'header', CHeaderDirective)
