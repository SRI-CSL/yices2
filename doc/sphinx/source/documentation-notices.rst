Documentation Licenses and Credits
==================================

These notices concern the API documentation's extensions, templates and
stylesheets. They do not replace Yices's ``NOTICES`` file, which describes
the solver and its other components.

Retained Sphinx material
-------------------------------

The ``cenum.py`` extension is adapted from Sphinx's C domain. The retained
``genindex.html``, ``localtoc.html``, ``relations.html`` and ``searchbox.html``
templates and ``epub.css`` stylesheet are also derived from Sphinx and carry
its 2007-2014 copyright notice. Local changes are recorded in these files.
The following complete primary notice is reproduced from Sphinx 1.3b2's
``LICENSE``. That release supplies a verified notice reference, not a claim
to identify every file's original import version.

.. literalinclude:: _static/licenses/SPHINX-1.3b2-LICENSE.txt
   :language: text

The corresponding Sphinx AUTHORS file is included unmodified:

.. literalinclude:: _static/licenses/SPHINX-1.3b2-AUTHORS.txt
   :language: text

Installed Sphinx theme
-------------------------------

HTML uses the stock ``classic`` theme installed with Sphinx, with the Yices
additions described below. The build includes the running Sphinx distribution's
complete license here; it does not substitute the historical notice above
for a newer builder's notice. EPUB also includes this notice in its text.

.. sphinx-build-license

.. only:: html

   In the HTML website, the **Sphinx builder** links at the bottom of the page
   also provide the version/checksum record and unmodified license file.

Yices additions
---------------

The new ``custom.css``, minimal ``layout.html`` navigation override and
``sphinx_notices.py`` notice-delivery extension are Copyright (c) 2026,
SRI International, under the BSD 3-Clause terms below. The new styling is
layered on the stock theme; the former inherited ``default.css`` and
``classic.css`` overrides are no longer distributed in this source tree.

.. literalinclude:: _static/licenses/YICES-BSD-3-Clause.txt
   :language: text

The Yices logo, favicon and pretty-printing illustrations are SRI International
material, separate from the Sphinx-derived files above. These notices do not
grant permission to use SRI names or marks to endorse another product.

Other documentation extension
-----------------------------

``cheader.py`` was written by Arto Bendiken and released into the public
domain, as its source header states.
