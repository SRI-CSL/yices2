# Building the API documentation

Use Python 3.8 or later and a compatible Sphinx installation. The configuration
requires Sphinx 1.8 or later for `add_css_file`; modern Sphinx versions use
their native C-domain enum support. The retained `cenum.py` adapter is loaded
only before Sphinx 3. Compatibility with every older Sphinx/Python combination
is not implied. The November 2026 style repair was previewed with Sphinx 8.2.3;
use the separately recorded release tool lock for a publication build.

For a local preview, choose a fresh output directory and run from this directory:

```sh
sphinx-build -b html source /absolute/path/to/new-api-preview
```

The installed stock `classic` theme supplies the base styles and layout.
`source/_static/custom.css` and theme options supply new Yices styling; do not
restore the former `default.css` or `classic.css` overrides. The small layout
override only adds navigation links through Sphinx's template interface.
The build extension adds `custom.css` through Sphinx's public stylesheet API
for HTML builders; EPUB keeps its separate theme and retained stylesheet.

`source/documentation-notices.rst` and `source/_static/licenses/` retain the
complete historical Sphinx notice, AUTHORS and the new additions' BSD terms.
The `sphinx_notices` extension includes the running builder's full Sphinx
license and version/checksum in the notices page. HTML additionally gets
unmodified text copies under `_static/licenses/`; EPUB embeds the notices
and AUTHORS in its text instead of plain-text attachments. The extension
stops the build if that license cannot be identified. Install Sphinx with its
distribution metadata and license intact. Deliver the entire output tree,
including the licenses directory and documentation-notices page.

Before publication, inspect navigation, search, index, representative API
pages, code and tables at desktop and narrow widths; check the five retained
SRI graphics and the license links. This source change does not rewrite or
assert clearance of historical Git revisions or older rendered sites.
