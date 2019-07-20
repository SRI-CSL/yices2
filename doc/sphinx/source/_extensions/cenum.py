# -*- coding: utf-8 -*-
#
# Support for enums in the C domain
# 
# Adds a directive for referencing/describing an enum element as in
#   .. c:enum:: STATUS_UNSAT
#
# Adds a role to refer to these:
#   :c:enum:`STATUS_UNSAT`
#
# This code is basaed on
#    sphinx/domains/__init__.py
#    sphinx/domains/c.py
#

from docutils.parsers.rst import Directive, directives

from sphinx import addnodes
from sphinx.roles import XRefRole
from sphinx.util.nodes import make_refnode
from sphinx.locale import l_, _
from sphinx.domains import ObjType
from sphinx.domains.c import CDomain, CObject, CXRefRole

class CEnumDirective(Directive):
  has_content = True
  required_arguments = 1
  optional_arguments = 0
  final_argument_whitespace = False
  option_spec = {
    'noindex': directives.flag,
  }
  domain = 'c'
  objtype = 'enum'

  def run(self):
    '''Processes a directive such as

        .. c:enum:: NAME

           blah, blah, blah.

        This generates:

          <desc desctype="enum" domain="c" ...>
           <desc_signature first="True" ids="c.NAME" names="c.NAME">
            <desc_name>NAME</desc_name>
           </desc_signature>
           <desc_content>
            <paragraph>blah, blah, blah</paragraph>
           </desc_content>
          <desc>

        Unless option :noindex: is given, this also creates an
        index node:

          <index entries={('single', 'NAME C(enum)', 'NAME', '')]/>

        We also add the pair (env.docname, 'enum') to

           env.domaindata['c']['objects]

        so that the CDomain resolve_xref and resolve_any_xref can
        later fix the reference :c:enum:`NAME`.

    '''
    env = self.state.document.settings.env
    name = self.arguments[0].strip()
    noindex = 'noindex' in self.options
    resultnodes = []

    signode = addnodes.desc_signature(name, '');
    signode['first'] = True
    signode.append(addnodes.desc_name(name, name))

    target_name = 'c.' + name
    if target_name not in self.state.document.ids:
        signode['names'].append(target_name)
        signode['ids'].append(target_name)
        self.state.document.note_explicit_target(signode)
        inv = env.domaindata['c']['objects']
        if name in inv:
            self.state_machine.reporter.warning(
                'duplicate C object description of %s, ' % name + 
                'other instance in ' + env.doc2path(inv[name][0]),
                line=self.lineno)
        inv[name] = (env.docname, 'enum')

    if not noindex:
        index_text = _('%s (C enum)') % name
        index_node = addnodes.index(entries=[('single', index_text, target_name, '', None)])
        resultnodes.append(index_node)

    node = addnodes.desc()
    node.document = self.state.document
    node['domain'] = self.domain
    node['objtype'] = self.objtype
    node['desctype'] = self.objtype
    node['noindex'] = noindex
    node.append(signode)

    contentnode = addnodes.desc_content();
    node.append(contentnode)
    self.state.nested_parse(self.content, self.content_offset, contentnode)

    resultnodes.append(node)

    return resultnodes

#
# We override CDomain since it doesn't know of the 'c:enum' role or
# the 'c:enum:: directive.
#
class ExtCDomain(CDomain):
    object_types = {
        'enum':     ObjType(l_('enum'),     'enum'),
        'function': ObjType(l_('function'), 'func'),
        'member':   ObjType(l_('member'),   'member'),
        'macro':    ObjType(l_('macro'),    'macro'),
        'type':     ObjType(l_('type'),     'type'),
        'var':      ObjType(l_('variable'), 'data'),
    }
    directives = {
        'enum':     CEnumDirective,
        'function': CObject,
        'member':   CObject,
        'macro':    CObject,
        'type':     CObject,
        'var':      CObject,
    }
    roles = {
        'enum':   XRefRole(),
        'func' :  CXRefRole(fix_parens=True),
        'member': CXRefRole(),
        'macro':  CXRefRole(),
        'data':   CXRefRole(),
        'type':   CXRefRole(),
    }


def setup(app):
  app.require_sphinx('1.3')
  app.override_domain(ExtCDomain)
