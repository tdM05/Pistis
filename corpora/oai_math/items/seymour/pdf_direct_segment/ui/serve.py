#!/usr/bin/env python3
"""Serve the PDF-direct segmentation UI. Run: python3 serve.py [port].
Serves the parent dir (so ../paper.pdf and ../tree.json are reachable) and
accepts POST /save to write ../tree.json."""
import http.server
import json
import os
import socketserver
import subprocess
import sys
import urllib.parse

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8780
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # pdf_direct_segment/
TREE = os.path.join(ROOT, "tree.json")


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *a, **k):
        super().__init__(*a, directory=ROOT, **k)

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            self.path = "/ui/index.html"
        elif self.path in ("/app.js", "/style.css"):
            self.path = "/ui" + self.path
        elif self.path == "/lean-files":
            return self.send_lean_files()
        elif self.path.startswith("/align"):
            return self.send_align()
        return super().do_GET()

    def send_align(self):
        """Align a def/theorem box against its Lean decl: shell to the Node
        driver (which elaborates Lean, cached) and return its JSON. Reads the box
        id from the ?id= query. May take a while on the FIRST call (Lean run)."""
        q = urllib.parse.urlparse(self.path).query
        box_id = urllib.parse.parse_qs(q).get("id", [""])[0]
        if not box_id:
            self.send_error(400, "missing id"); return
        try:
            out = subprocess.run(
                ["node", "tools/inspect.js", "--align-json", box_id],
                cwd=ROOT, capture_output=True, text=True, timeout=330,
            )
            body = (out.stdout or '{"ok":false,"reason":"no output"}').encode()
            if out.returncode != 0 and not out.stdout:
                body = json.dumps({"ok": False, "reason": (out.stderr or "align failed")[:800]}).encode()
        except subprocess.TimeoutExpired:
            body = b'{"ok":false,"reason":"lean extract timed out"}'
        except Exception as e:
            body = json.dumps({"ok": False, "reason": str(e)}).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def send_lean_files(self):
        """List every .lean file under lean/ (relative paths), sorted."""
        base = os.path.join(ROOT, "lean")
        files = []
        for dp, _dn, fn in os.walk(base):
            for f in fn:
                if f.endswith(".lean"):
                    rel = os.path.relpath(os.path.join(dp, f), ROOT)
                    files.append(rel.replace(os.sep, "/"))
        files.sort()
        body = json.dumps(files).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self):
        if self.path != "/save":
            self.send_error(404); return
        n = int(self.headers.get("Content-Length", 0))
        try:
            data = json.loads(self.rfile.read(n) or b"{}")
            with open(TREE, "w") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            self.send_response(200); self.send_header("Content-Type", "application/json"); self.end_headers()
            self.wfile.write(b'{"ok":true}')
        except Exception as e:
            self.send_response(500); self.send_header("Content-Type", "application/json"); self.end_headers()
            self.wfile.write(json.dumps({"ok": False, "error": str(e)}).encode())


class Server(socketserver.TCPServer):
    allow_reuse_address = True


if __name__ == "__main__":
    os.chdir(ROOT)
    try:
        httpd = Server(("127.0.0.1", PORT), Handler)
    except OSError:
        PORT += 1; httpd = Server(("127.0.0.1", PORT), Handler)
    with httpd:
        print(f"serving {ROOT}\nopen  http://127.0.0.1:{PORT}/")
        httpd.serve_forever()
