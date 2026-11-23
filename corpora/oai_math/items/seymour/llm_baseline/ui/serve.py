#!/usr/bin/env python3
"""Serve the NAIVE-baseline findings in the real inspector UI.

Run:  python3 ui/serve.py [port] [--level N]   (from the llm_baseline/ dir, or anywhere)

Serves the llm_baseline/ dir (so ../paper.pdf, ../schema.json, ../core.js, ../lean/
are reachable) and synthesizes GET /tree.json from findings/tree.level{N}.json, so
the unmodified inspector renders each finding as a highlighted box over the PDF.
Switch levels by restarting with a different --level. /save writes human review
(verdicts/edits) back to findings/tree.level{N}.json."""
import glob
import http.server
import json
import os
import re
import socketserver
import sys
import urllib.parse

args = [a for a in sys.argv[1:]]
default_level = 0
if "--level" in args:
    i = args.index("--level"); default_level = int(args[i + 1]); del args[i:i + 2]
PORT = int(args[0]) if args else 8790
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # llm_baseline/


def tree_path(level):
    return os.path.join(ROOT, "findings", f"tree.level{level}.json")


def available_levels():
    out = []
    for p in glob.glob(os.path.join(ROOT, "findings", "tree.level*.json")):
        m = re.search(r"tree\.level(\d+)\.json$", p)
        if m:
            out.append(int(m.group(1)))
    return sorted(out)


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *a, **k):
        super().__init__(*a, directory=ROOT, **k)

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def _json(self, obj, code=200):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _level(self):
        q = urllib.parse.urlparse(self.path).query
        v = urllib.parse.parse_qs(q).get("level", [str(default_level)])[0]
        try:
            return int(v)
        except ValueError:
            return default_level

    def do_GET(self):
        route = urllib.parse.urlparse(self.path).path
        if route in ("/", "/index.html"):
            self.path = "/ui/index.html"
        elif route in ("/app.js", "/style.css"):
            self.path = "/ui" + route
        elif route == "/levels":
            return self._json(available_levels())
        elif route == "/tree.json":
            level = self._level()
            try:
                with open(tree_path(level)) as f:
                    return self._json(json.load(f))
            except FileNotFoundError:
                return self._json({"id": "root", "pieces": [], "children": [],
                                   "_note": f"no findings/tree.level{level}.json — run: node run.js --level {level}"})
        elif route == "/lean-files":
            base = os.path.join(ROOT, "lean"); files = []
            for dp, _dn, fn in os.walk(base):
                for f in fn:
                    if f.endswith(".lean"):
                        files.append(os.path.relpath(os.path.join(dp, f), ROOT).replace(os.sep, "/"))
            files.sort(); return self._json(files)
        return super().do_GET()

    def do_POST(self):
        route = urllib.parse.urlparse(self.path).path
        if route != "/save":
            self.send_error(404); return
        level = self._level()
        n = int(self.headers.get("Content-Length", 0))
        try:
            data = json.loads(self.rfile.read(n) or b"{}")
            with open(tree_path(level), "w") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            self._json({"ok": True})
        except Exception as e:
            self._json({"ok": False, "error": str(e)}, 500)


class Server(socketserver.TCPServer):
    allow_reuse_address = True


if __name__ == "__main__":
    os.chdir(ROOT)
    try:
        httpd = Server(("127.0.0.1", PORT), Handler)
    except OSError:
        PORT += 1; httpd = Server(("127.0.0.1", PORT), Handler)
    with httpd:
        print(f"serving {ROOT} (default level {default_level}, available {available_levels()})\nopen  http://127.0.0.1:{PORT}/")
        httpd.serve_forever()
