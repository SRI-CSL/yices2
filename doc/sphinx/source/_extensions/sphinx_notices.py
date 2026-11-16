"""Deliver the actual builder's Sphinx license alongside its rendered assets.

Copyright (c) 2026, SRI International
SPDX-License-Identifier: BSD-3-Clause
Full terms: ../_static/licenses/YICES-BSD-3-Clause.txt
"""
import hashlib
from importlib import metadata
from pathlib import Path

import sphinx
from sphinx.errors import ExtensionError


def read_builder_license():
    try:
        distribution = metadata.distribution("Sphinx")
        candidates = [entry for entry in (distribution.files or ())
                      if entry.name in ("LICENSE", "LICENSE.rst", "LICENSE.txt")]
        if distribution.version != sphinx.__version__ or len(candidates) != 1:
            raise ValueError("cannot uniquely identify the running Sphinx distribution's license")
        text = Path(distribution.locate_file(candidates[0])).read_bytes()
        if b"License for Sphinx" not in text or b"Redistribution and use" not in text:
            raise ValueError("installed license does not contain the Sphinx grant")
    except (OSError, ValueError, metadata.PackageNotFoundError) as error:
        raise ExtensionError("Cannot deliver the Sphinx builder license: " + str(error)) from error
    return text


def inline_builder_license(app, docname, source):
    if docname != "documentation-notices":
        return
    marker = ".. sphinx-build-license"
    if source[0].count(marker) != 1:
        raise ExtensionError("Expected one installed-Sphinx notice placeholder")
    text = read_builder_license()
    notice = "Sphinx version: " + sphinx.__version__ + ". License SHA-256: ``" + hashlib.sha256(text).hexdigest() + "``.\n\n"
    notice += ".. code-block:: text\n\n" + "\n".join("   " + line for line in text.decode("utf-8").splitlines())
    source[0] = source[0].replace(marker, notice)


def copy_builder_license(app):
    # EPUB carries the inline page, not unmanifestable text attachments.
    if app.builder.format != "html" or app.builder.name.startswith("epub"):
        return
    text = read_builder_license()

    destination = Path(app.outdir) / "_static" / "licenses"
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "SPHINX-BUILD-LICENSE.txt").write_bytes(text)
    (destination / "SPHINX-BUILD.txt").write_text(
        "Sphinx version: " + sphinx.__version__ + "\n"
        "License: SPHINX-BUILD-LICENSE.txt\n"
        "License SHA-256: " + hashlib.sha256(text).hexdigest() + "\n",
        encoding="utf-8")
    app.add_css_file("custom.css")


def setup(app):
    app.connect("source-read", inline_builder_license)
    app.connect("builder-inited", copy_builder_license)
    return {"version": "1", "parallel_read_safe": True, "parallel_write_safe": True}
