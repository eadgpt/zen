#!/usr/bin/env python3
"""Static server for the zen garden. Same as `python3 -m http.server 8791`, but tells the browser never to
cache, so a plain refresh always picks up the latest zen.js / audio.js."""
import functools
import http.server
import os

PORT = 8791


class NoCacheHandler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-store, max-age=0")
        super().end_headers()


if __name__ == "__main__":
    root = os.path.dirname(os.path.abspath(__file__))
    handler = functools.partial(NoCacheHandler, directory=root)
    with http.server.ThreadingHTTPServer(("", PORT), handler) as httpd:
        print(f"Zen garden on http://localhost:{PORT}")
        httpd.serve_forever()
