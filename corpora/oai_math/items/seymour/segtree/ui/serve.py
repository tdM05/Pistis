#!/usr/bin/env python3
"""Serve the seg-tree UI. Run: python3 serve.py [port].

Serves the segtree/ dir (so source.tex and tree.json are reachable), and
accepts POST /save to write tree.json.
"""
import http.server
import importlib.util
import json
import os
import socketserver
import sys

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8770
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # segtree/
TREE = os.path.join(ROOT, "tree.json")

# load inject.py (sits in segtree/) for highlight-compile + validity
_spec = importlib.util.spec_from_file_location("inject", os.path.join(ROOT, "inject.py"))
inject = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(inject)


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *a, **k):
        super().__init__(*a, directory=ROOT, **k)

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def do_GET(self):
        if self.path == "/files":
            return self._json(200, {"files": inject.ALL_FILES, "tex": inject.TEX_FILES})
        # ui files live in ui/; map bare / to ui/index.html
        if self.path in ("/", "/index.html"):
            self.path = "/ui/index.html"
        elif self.path in ("/app.js", "/style.css", "/render.js"):
            self.path = "/ui" + self.path
        return super().do_GET()

    def _json(self, code, obj):
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(obj).encode())

    def _body(self):
        n = int(self.headers.get("Content-Length", 0))
        return json.loads(self.rfile.read(n) or b"{}")

    def do_POST(self):
        try:
            if self.path == "/save":
                data = self._body()
                with open(TREE, "w") as f:
                    json.dump(data, f, indent=2, ensure_ascii=False)
                return self._json(200, {"ok": True})

            if self.path == "/validate":
                b = self._body()
                ok, reason = inject.validate_span(b["file"], int(b["s"]), int(b["e"]))
                return self._json(200, {"ok": ok, "reason": reason})

            if self.path == "/render":
                # body: {boxes:[{file,s,e,color}]} -> one PDF (whole paper grey,
                # the given spans coloured)
                boxes = self._body().get("boxes", [])
                ok, pdf, log = inject.compile_tree(boxes)
                if ok:
                    data = open(pdf, "rb").read()
                    self.send_response(200)
                    self.send_header("Content-Type", "application/pdf")
                    self.send_header("Content-Length", str(len(data)))
                    self.end_headers()
                    self.wfile.write(data)
                    return
                return self._json(200, {"ok": False, "log": log})

            if self.path == "/whereis":
                # body: {page, x, y} in PDF points -> {file, line} (reverse sync)
                b = self._body()
                hit = inject.reverse_sync(int(b["page"]), float(b["x"]), float(b["y"]))
                return self._json(200, hit or {"file": None})

            self.send_error(404)
        except Exception as e:
            self._json(500, {"ok": False, "error": str(e)})


class Server(socketserver.TCPServer):
    allow_reuse_address = True


if __name__ == "__main__":
    os.chdir(ROOT)
    try:
        httpd = Server(("127.0.0.1", PORT), Handler)
    except OSError:
        PORT += 1
        httpd = Server(("127.0.0.1", PORT), Handler)
    # Prebuild the LaTeX work dir in the background at startup, so the first
    # Render isn't a cold ~9s surprise (or a timeout). Renders before it finishes
    # still work — ensure_work() is idempotent and will just no-op.
    import threading
    threading.Thread(target=inject.ensure_work, daemon=True).start()
    with httpd:
        print(f"serving {ROOT}")
        print(f"open  http://127.0.0.1:{PORT}/")
        print("(prebuilding LaTeX work dir in background…)")
        httpd.serve_forever()
