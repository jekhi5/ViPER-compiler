#!/usr/bin/env python3
"""
serve_docs.py — Serves built documentation over HTTP on a forwarded port.
No external dependencies required.

Usage:
    python serve_docs.py [port]

Default port: 8080
"""

import http.server
import os
import sys
from functools import partial

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

DOCS_ROOT = os.path.join("..", "docs", "_html", "viper")
INDEX_FILE = "index.html"
DEFAULT_PORT = 8080
BIND_HOST = "0.0.0.0"  # Accept connections on all interfaces (needed for port forwarding)


# ---------------------------------------------------------------------------
# Custom handler
# ---------------------------------------------------------------------------

class DocsHandler(http.server.SimpleHTTPRequestHandler):
    """Serves files from DOCS_ROOT, with a clean index fallback."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=DOCS_ROOT, **kwargs)

    def do_GET(self):
        # Redirect bare "/" to the main index
        if self.path in ("", "/"):
            self.send_response(302)
            self.send_header("Location", f"/{INDEX_FILE}")
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
    if len(sys.argv) > 1:
        try:
            port = int(sys.argv[1])
        except ValueError:
            sys.exit(f"Error: port must be an integer, got {sys.argv[1]!r}")

    if not os.path.isdir(DOCS_ROOT):
        sys.exit(
            f"Error: docs directory not found:\n  {DOCS_ROOT}\n"
            "Build your documentation first, or adjust DOCS_ROOT in this script."
        )

    handler = partial(DocsHandler)

    with http.server.ThreadingHTTPServer((BIND_HOST, port), handler) as httpd:
        print(f"Serving docs from : {DOCS_ROOT}")
        print(f"Listening on      : http://{BIND_HOST}:{port}")
        print(f"Open in browser   : http://localhost:{port}/")
        print("Press Ctrl+C to stop.\n")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\nShutting down.")


if __name__ == "__main__":
    main()