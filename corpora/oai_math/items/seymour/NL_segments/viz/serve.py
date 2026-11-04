#!/usr/bin/env python3
"""Serve the NL-structure viz. Run from this dir: python3 serve.py [port].

Serves the parent directory so the viz can fetch ../segments.json.
"""
import http.server
import os
import socketserver
import sys

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8765
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # NL_segments/


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *a, **k):
        super().__init__(*a, directory=ROOT, **k)

    def end_headers(self):
        self.send_header('Cache-Control', 'no-store')
        super().end_headers()


class Server(socketserver.TCPServer):
    # rebind immediately even if the previous socket is still in TIME_WAIT
    allow_reuse_address = True


if __name__ == '__main__':
    os.chdir(ROOT)
    try:
        httpd = Server(('127.0.0.1', PORT), Handler)
    except OSError as e:
        print(f"port {PORT} busy ({e}); trying {PORT + 1} ...")
        PORT += 1
        httpd = Server(('127.0.0.1', PORT), Handler)
    with httpd:
        print(f"serving {ROOT}")
        print(f"open  http://127.0.0.1:{PORT}/viz/")
        httpd.serve_forever()
