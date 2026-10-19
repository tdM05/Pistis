#!/usr/bin/env python3
"""One viewer for every level of the tree.

The point of the K-Pistis model is that a proof step and an atomic label are the SAME object, so
there is one page and it renders a unit — whichever unit. The root shows `Proof.lean` against the
whole lemma, with the proof steps as regions; click into a step and the identical widget shows that
step's Lean against that step's prose, with the atomic pieces as regions; click again and you are
looking at `D + τ • Matrix.single s j 1` against `D+\\tau e_s e_j^{\\mathsf T}`. The breadcrumb is the
only thing that changes.

Read-write for the two things a human is here to decide — an edge's verdict and its reason, and
whether a unit is `done`. Read-only for everything else: regions are authored in
`annotate_item1.py`, where they are named by the text they cover and so cannot silently slide, and
the targets are derived in `build.py`. The UI cannot cut a span, which is deliberate — a span drawn
by dragging is a span nobody can re-derive.

    GET  /                          the page
    GET  /app.js  /style.css        its parts
    GET  /api/tree?item=item1       the rollup tree (sidebar + badges)
    GET  /api/unit?item=&path=      one unit: targets, regions, C_N, placement, edges, status
    POST /api/edge                  {item, path, i, v, why}   — judge one edge
    POST /api/done                  {item, path, done}        — mark a unit finished

Run:  python3 kpistis/ui/serve.py        # then open http://localhost:8010
"""
from __future__ import annotations

import argparse
import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import model                                                               # noqa: E402

MIME = {".html": "text/html", ".js": "text/javascript", ".css": "text/css"}


def items() -> list[str]:
    return sorted(p.name for p in (model.ROOT / "units").iterdir() if (p / "root").is_dir())


def unit_payload(item: str, path: str) -> dict:
    unit = model.load(item, path)
    st = model.status(unit)
    root_tn = model.load(item, "root")["T_N"]

    def regions(kind, target, locs, cites=None):
        out = []
        for i, spans in enumerate(unit[kind]):
            norm = [[a, b] for a, b in model.normalize(spans)]
            out.append({"idx": i, "loc": (locs[i] if i < len(locs) else f"{kind[-1]}{i}"),
                        "spans": norm, "text": model.region_text(unit[target], spans),
                        # `C_N` rides on the REGION, because that is what an edge names. At the root
                        # the unit's own target is the whole paper and could have no context at all;
                        # its regions have thirteen edges' worth.
                        "C_N": [{"spans": c["spans"], "why": c.get("why", ""),
                                 "text": model.cn_text(root_tn, c)}
                                for c in (cites[i] if cites and i < len(cites) else [])]})
        return out

    crumbs, at = [], []
    for part in path.split("/"):
        at.append(part)
        crumbs.append({"path": "/".join(at), "loc": part})
    return {
        "item": item, "path": path,
        "loc": unit.get("loc", path), "title": unit.get("title", ""),
        "category": unit.get("category", ""), "child_category": unit.get("child_category", ""),
        "provenance": unit.get("provenance", {}), "done": bool(unit.get("done")),
        "T_F": unit["T_F"], "T_N": unit["T_N"],
        "F": regions("S_F", "T_F", unit.get("F_locs", [])),
        "N": regions("S_N", "T_N", unit.get("N_locs", []), unit["C_N"]),
        "edges": unit["edges"], "children": unit["children"],
        "crumbs": crumbs, "status": st,
        # The two different things called context, kept apart because they are different.
        #
        # `C_N` is AUTHORED: the prose of the paper an NL region has to be read against, chosen by a
        # person, each citation carrying its reason. Stored as spans into the root's `T_N`, so the
        # text is sliced here and never transcribed anywhere. It is served on each `N` region above
        # rather than on the unit, so the edge on screen always has its own context.
        # `placement` is DERIVED: where this unit's target sits inside each ancestor, inside
        # `Proof.lean` and inside the paper, by arithmetic on the chain (`model.ancestry`). It is the
        # only formal-side context there is, and there is nothing authored in it. Empty at the root.
        "placement": model.ancestry(item, path),
    }


class Handler(BaseHTTPRequestHandler):
    def log_message(self, format: str, *args) -> None:          # the console is for the gate's output
        pass

    def _send(self, code, body: bytes, ctype="application/json"):
        self.send_response(code)
        self.send_header("Content-Type", ctype + ("; charset=utf-8" if "text" in ctype else ""))
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, code=200):
        self._send(code, json.dumps(obj, ensure_ascii=False).encode("utf-8"))

    def do_GET(self):
        url = urlparse(self.path)
        q = {k: v[0] for k, v in parse_qs(url.query).items()}
        route = url.path
        try:
            if route in ("/", "/index.html"):
                return self._send(200, (HERE / "index.html").read_bytes(), "text/html")
            if route in ("/app.js", "/style.css"):
                return self._send(200, (HERE / route.lstrip("/")).read_bytes(),
                                  MIME[Path(route).suffix])
            if route == "/api/tree":
                item = q.get("item") or items()[0]
                return self._json({"item": item, "items": items(),
                                   "tree": model.rollup(item)})
            if route == "/api/unit":
                return self._json(unit_payload(q.get("item", "item1"), q.get("path", "root")))
        except FileNotFoundError as err:
            return self._json({"error": str(err)}, 404)
        except (ValueError, KeyError) as err:
            return self._json({"error": f"{type(err).__name__}: {err}"}, 400)
        self._json({"error": f"no route {route}"}, 404)

    def do_POST(self):
        route = urlparse(self.path).path
        try:
            body = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0)) or 0))
            unit = model.load(body["item"], body["path"])
            if route == "/api/edge":
                e = unit["edges"][int(body["i"])]
                v = body.get("v")
                e["v"] = None if v in (None, "", "null") else int(v)
                e["why"] = str(body.get("why", "")).strip()
            elif route == "/api/done":
                unit["done"] = bool(body["done"])
            else:
                return self._json({"error": f"no route {route}"}, 404)
            errs = model.edge_errors(unit)
            if errs:
                return self._json({"error": "; ".join(errs)}, 400)
            model.save(unit)
            return self._json(unit_payload(body["item"], body["path"]))
        except (ValueError, KeyError, IndexError, TypeError) as err:
            return self._json({"error": f"{type(err).__name__}: {err}"}, 400)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Serve the K-Pistis viewer.")
    ap.add_argument("--port", type=int, default=8010)
    args = ap.parse_args(argv)
    srv = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    print(f"K-Pistis viewer on http://localhost:{args.port}   (items: {', '.join(items())})")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
