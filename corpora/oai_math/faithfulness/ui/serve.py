#!/usr/bin/env python3
"""Local align-then-label server for the openai/math corpus.

Vendored from faithfulness-dataset (`src/ui/serve.py`) and scoped to this corpus: `REPO` is
`corpora/oai_math/` (the Lake package root, so the version pin still reads its real
`lean-toolchain` / `lake-manifest.json`), and datapoints live at
`items/item<N>/align/<unit>/artifacts/`.

The workflow is unchanged: **given the targets (T_F, T_N), a human labels from scratch.** This server
serves one page (index.html + proof_pane.js) — `Main.lean` in the left panel, the selected unit's
align-then-label view in the right — plus a JSON API over the datapoint artifacts.

A datapoint is any folder containing an ``artifacts/`` subtree. It has two "targets" the labeler is
given:

    T_F  (formal/T_F.lean)   the formal claim      -- provided, then fixed
    T_N  (nl/T_N.txt)        the NL text           -- provided

For this corpus both targets are GENERATED mechanically from the item's `Main.lean` + `split.json` by
`faithfulness/gen_datapoints.py`, so the proof panel and the datapoints can never drift from the proof.
Setting targets by hand (POST /api/targets) still works for ad-hoc datapoints.

Everything else is **authored from scratch** in the UI and saved here:

    S_F, S_N, C_F.items, C_N, I, R, lambda, label

T_F is normalized on entry so it has no structural newlines — its segmentation is the spans of S_F,
never newlines.

Differences from the upstream server, all because this corpus has no `cf_extract` binary and no
`proof-read` CLI:
  * `C_F.available` (upstream: depth-1 Lean constants of T_F) is left empty. `C_F.items` — the
    hand-authored denotations, which is what the labeler actually links — is unaffected.
  * `/api/expand` and `/api/generate` (auto-draft) are gone; the UI hides their buttons.
  * `/api/overview` is new: the proof outline the left panel renders.

Endpoints:
    GET  /  /label  ?path=REL           -> index.html (proof on the left, that unit's labeler on the right)
    GET  /proof_pane.js                 -> the left panel's script
    GET  /api/overview                  -> the proof outline + per-unit datapoint status
    GET  /api/datapoints                -> [{path, label, has_targets, done}, ...]
    GET  /api/datapoint?path=REL        -> the full bundle for one datapoint
    POST /api/save?path=REL             -> write back the authored artifacts
    POST /api/targets?path=REL          -> set/normalize T_F+T_N
    POST /api/create?path=REL           -> create an empty datapoint skeleton

Run:  python3 faithfulness/ui/serve.py   # from corpora/oai_math, open localhost:8000
"""
from __future__ import annotations

import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse, parse_qs

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent                      # corpus root (contains lakefile.lean)
sys.path.insert(0, str(REPO / "faithfulness"))  # shared annotation IO, formats, proof outline
from tf_norm import normalize_tf                # noqa: E402
from alignment_data import (                    # noqa: E402
    find_datapoints as _find_datapoints, load_bundle, _has_targets, _read_json,
)
from check_coverage import check_bundle          # noqa: E402
from pistis_proof import proof_outline           # noqa: E402


# --------------------------------------------------------------------------
# version pin (toolchain + mathlib/batteries revs)
# --------------------------------------------------------------------------
def detect_versions() -> dict:
    out: dict = {}
    tc = REPO / "lean-toolchain"
    lm = REPO / "lake-manifest.json"
    if tc.exists():
        out["toolchain"] = tc.read_text(encoding="utf-8").strip()
    if lm.exists():
        try:
            man = json.loads(lm.read_text(encoding="utf-8"))
            out["packages"] = {p["name"]: p.get("rev")
                               for p in man.get("packages", [])
                               if p["name"] in ("mathlib", "batteries")}
        except (json.JSONDecodeError, KeyError):
            pass
    return out


def version_text(versions: dict) -> str:
    return (versions.get("toolchain", "") + "\n" +
            "".join(f"{k} {v}\n" for k, v in versions.get("packages", {}).items()))


# --------------------------------------------------------------------------
# datapoint discovery / IO  (cached for speed)
# --------------------------------------------------------------------------
_dp_cache: list[dict] | None = None
_valid_cache: dict[str, tuple[bool, list[str]]] = {}


def _invalidate_dp(path: str | None = None) -> None:
    global _dp_cache
    _dp_cache = None
    if path is not None:
        _valid_cache.pop(path, None)


def find_datapoints() -> list[dict]:
    global _dp_cache
    if _dp_cache is None:
        _dp_cache = _find_datapoints()
    result = []
    for item in _dp_cache:
        entry = dict(item)
        if entry["done"]:
            valid, reasons = _valid_cache.get(entry["path"], (True, []))
            entry.update(valid=valid, invalid_reasons=reasons)
        else:
            entry.update(valid=True, invalid_reasons=[])
        result.append(entry)
    return result


def _dump(p: Path, obj) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n",
                 encoding="utf-8")


def _ensure_skeleton(art: Path) -> None:
    """Create the artifacts tree with empty authored files (idempotent)."""
    for d in ("formal", "nl", "relation"):
        (art / d).mkdir(parents=True, exist_ok=True)
    defaults = {
        art / "formal" / "S_F.json": [],
        art / "nl" / "S_N.json": [],
        art / "nl" / "C_N.json": [],
        art / "nl" / "I.json": [],
        art / "relation" / "R.json": [],
        art / "relation" / "lambda.json": [],
    }
    for p, val in defaults.items():
        if not p.exists():
            _dump(p, val)
    if not (art / "label.txt").exists():
        (art / "label.txt").write_text("NaN\n", encoding="utf-8")


def create_datapoint(rel: str) -> dict:
    art = REPO / rel / "artifacts"
    _ensure_skeleton(art)
    _invalidate_dp()
    return {"ok": True, "path": rel}


def save_bundle(rel: str, data: dict) -> dict:
    """Save UTF-16 annotations while retaining fixed documents and inventories."""
    stored = load_bundle(rel)
    incoming = {**stored, **{key: data[key] for key in
                ("S_F", "S_N", "C_N", "I", "R", "lambda", "label", "done")}}
    incoming["C_F"] = {**stored["C_F"], "items": data["C_F"]["items"]}
    errors, _ = check_bundle(incoming, finishing=bool(data.get("done")))
    if errors:
        raise ValueError("; ".join(errors))
    art = REPO / rel / "artifacts"
    for folder, name, key in (("formal", "S_F", "S_F"), ("formal", "C_F", "C_F"),
                              ("nl", "S_N", "S_N"), ("nl", "C_N", "C_N"), ("nl", "I", "I"),
                              ("relation", "R", "R"), ("relation", "lambda", "lambda")):
        _dump(art / folder / (name + ".json"), incoming[key])
    (art / "label.txt").write_text(incoming["label"] + "\n", encoding="utf-8")
    done = bool(incoming.get("done"))
    (art / "done.txt").write_text(("true" if done else "false") + "\n",
                                  encoding="utf-8")
    _invalidate_dp(rel)
    if done:
        _valid_cache[rel] = (True, [])
    return {"path": rel, "label": incoming["label"],
            "has_targets": _has_targets(art), "done": done,
            "valid": _valid_cache.get(rel, (True, []))[0],
            "invalid_reasons": _valid_cache.get(rel, (True, []))[1]}


def set_targets(rel: str, data: dict) -> dict:
    """Normalize + write T_F/T_N and the version pin, preserving any curated C_F items.

    Upstream this also re-derived `C_F.available` (the depth-1 Lean constants of T_F) by shelling out
    to the `cf_extract` binary. This corpus has no such binary, so `available` stays empty; it is a
    read-only convenience list anyway. The curated `items` — the denotations the labeler actually
    links — are authored in the UI (or seeded by gen_datapoints.py) and are kept across a re-set, so
    re-pasting a target never silently discards formal context.
    """
    art = REPO / rel / "artifacts"
    _ensure_skeleton(art)
    tf_path = art / "formal" / "T_F.lean"
    tf_path.write_text(normalize_tf(data.get("T_F", "")), encoding="utf-8")
    (art / "nl" / "T_N.txt").write_text(
        data.get("T_N", "").strip() + "\n", encoding="utf-8")

    versions = detect_versions()
    (art / "formal" / "version.txt").write_text(version_text(versions),
                                                 encoding="utf-8")
    prev = _read_json(art / "formal" / "C_F.json", {})
    _dump(art / "formal" / "C_F.json",
          {"pin": versions, "available": [], "items": prev.get("items", [])})
    _invalidate_dp(rel)
    return {"ok": True, "cf_error": "", "bundle": load_bundle(rel)}


# --------------------------------------------------------------------------
# proof overview
# --------------------------------------------------------------------------
def overview() -> dict:
    """Every item's proof outline, joined to the align-then-label status of each unit.

    `proof_outline` is the structure (read fresh from Main.lean + split.json each request, so editing
    the proof is reflected on reload); the datapoint list supplies label/done/has_targets. A unit whose
    datapoint has not been generated yet comes back with `datapoint: null` so the panel can say so
    rather than linking to a 404.
    """
    status = {d["path"]: d for d in find_datapoints()}
    items = []
    for item_dir in sorted((REPO / "items").glob("item*")):
        if not (item_dir / "Main.lean").exists():
            continue
        rel = str(item_dir.relative_to(REPO))
        out = proof_outline(item_dir)
        for unit in out["units"]:
            unit["datapoint"] = status.get(f"{rel}/align/{unit['id']}")
        out["path"] = rel
        items.append(out)
    return {"items": items}


# --------------------------------------------------------------------------
# HTTP
# --------------------------------------------------------------------------
class Handler(BaseHTTPRequestHandler):
    def _send(self, code: int, body: bytes, ctype: str) -> None:
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, code: int = 200) -> None:
        self._send(code, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                   "application/json; charset=utf-8")

    def _body(self) -> dict:
        length = int(self.headers.get("Content-Length", 0))
        return json.loads(self.rfile.read(length).decode("utf-8")) if length else {}

    def do_GET(self):  # noqa: N802
        u = urlparse(self.path)
        q = parse_qs(u.query)
        try:
            # One page, two panels: `Main.lean` on the left, the selected unit's align-then-label
            # view on the right. `?path=` picks the unit, so the old /label URLs still work.
            if u.path in ("/", "/label", "/index.html"):
                return self._send(200, (HERE / "index.html").read_bytes(),
                                  "text/html; charset=utf-8")
            if u.path == "/proof_pane.js":
                return self._send(200, (HERE / "proof_pane.js").read_bytes(),
                                  "application/javascript; charset=utf-8")
            if u.path == "/api/overview":
                return self._json(overview())
            if u.path == "/api/datapoints":
                return self._json(find_datapoints())
            if u.path == "/api/datapoint":
                return self._json(load_bundle(q["path"][0]))
        except Exception as e:  # noqa: BLE001
            return self._json({"error": repr(e)}, 500)
        return self._json({"error": "not found"}, 404)

    def do_POST(self):  # noqa: N802
        u = urlparse(self.path)
        q = parse_qs(u.query)
        try:
            if u.path == "/api/save":
                meta = save_bundle(q["path"][0], self._body())
                return self._json({"ok": True, "meta": meta})
            if u.path == "/api/targets":
                return self._json(set_targets(q["path"][0], self._body()))
            if u.path == "/api/create":
                return self._json(create_datapoint(q["path"][0]))
        except Exception as e:  # noqa: BLE001
            return self._json({"error": repr(e)}, 500)
        return self._json({"error": "not found"}, 404)

    def log_message(self, format, *args):  # quiet
        pass


def main() -> int:
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    srv = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    print(f"pistis align-then-label: http://localhost:{port}  (corpus: {REPO})")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
