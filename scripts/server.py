#!/usr/bin/env python3
"""
serve_docs.py — Serves built documentation over HTTP on a forwarded port.
No external dependencies required.

Usage:
    python serve_docs.py [port] [--coverage | -c]
"""

import http.server
import os
import sys
from functools import partial

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

DOCS_ROOT = "docs/_html"
COVERAGE_ROOT = "_coverage"  # placeholder: point this at your coverage report output dir
DOCS_INDEX_FILE = "viper/index.html"
COVERAGE_INDEX_FILE = "index.html"
DEFAULT_PORT = 8080
BIND_HOST = "0.0.0.0"  # Accept connections on all interfaces (needed for port forwarding)


# ---------------------------------------------------------------------------
# Custom handler
# ---------------------------------------------------------------------------

class DocsHandler(http.server.SimpleHTTPRequestHandler):
    """Serves files from a given root directory, with a clean index fallback."""

    def __init__(self, *args, directory=None, index_file=DOCS_INDEX_FILE, **kwargs):
        self.index_file = index_file
        super().__init__(*args, directory=directory, **kwargs)

    def do_GET(self):
        # Redirect bare "/" to the main index
        if self.path in ("", "/"):
            self.send_response(302)
            self.send_header("Location", f"/{self.index_file}")
            self.end_headers()
            return
        super().do_GET()

    def log_message(self, fmt, *args):
        # Slightly tidier log lines
        sys.stdout.write(f"[docs] {self.address_string()} — {fmt % args}\n")
        sys.stdout.flush()


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    port = DEFAULT_PORT
    serve_root = DOCS_ROOT
    index_file = DOCS_INDEX_FILE

    args = sys.argv[1:]
    for arg in args:
        if arg in ("--coverage", "-c"):
            serve_root = COVERAGE_ROOT
            index_file = COVERAGE_INDEX_FILE
        else:
            try:
                port = int(arg)
            except ValueError:
                sys.exit(f"Error: unrecognized argument {arg!r}")

    if not os.path.isdir(serve_root):
        sys.exit(
            f"Error: directory not found:\n  {serve_root}\n"
            "Build the corresponding output first, or adjust the path in this script."
        )

    handler = partial(DocsHandler, directory=serve_root, index_file=index_file)

    with http.server.ThreadingHTTPServer((BIND_HOST, port), handler) as httpd:
        print(f"Serving docs from : {serve_root}")
        print(f"Listening on      : http://{BIND_HOST}:{port}")
        print(f"Open in browser   : http://localhost:{port}/")
        print("Press Ctrl+C to stop.\n")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\nShutting down.")


if __name__ == "__main__":
    main()