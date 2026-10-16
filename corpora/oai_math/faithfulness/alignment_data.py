"""Shared dataset IO and validation of UTF-16 annotation regions.

Vendored from faithfulness-dataset (`src/alignment_data.py`) into this corpus so the align-then-label
work stays isolated to openai/math. `REPO` resolves to `corpora/oai_math/` — the Lake package root —
exactly as it resolved to the dataset repo root there, so datapoint paths read
`items/item<N>/align/<unit>`. The only edits are this docstring and `_gt` in `_SKIP_DIRS`.
"""
from __future__ import annotations

import json
import os
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
BOT = "⊥"
FORMAL_KINDS = {"S_F", "C_F"}
NL_KINDS = {"S_N", "C_N", "I"}
ALL_KINDS = FORMAL_KINDS | NL_KINDS
DEFAULT_FORMAT = {"offset_unit": "utf16", "coverage": "complete"}
# `_gt` holds each item's ground-truth/baseline proof. Reading it is disqualifying contamination, so
# the datapoint walk never descends into it.
_SKIP_DIRS = {".git", ".lake", "lake-packages", "build", ".venv",
              "node_modules", "__pycache__", ".cache", "_gt"}


def bundle_format(data):
    """Validate format metadata; absent metadata means complete coverage."""
    value = data.get("format", DEFAULT_FORMAT)
    if (not isinstance(value, dict) or set(value) != {"offset_unit", "coverage"}
            or value["offset_unit"] != "utf16"
            or value["coverage"] not in ("selective", "complete")):
        raise ValueError("format must specify offset_unit 'utf16' and coverage 'selective' or 'complete'")
    return dict(value)


def read_format(variant):
    path = Path(variant) / "artifacts/format.json"
    return bundle_format({"format": _read_json(path, None)} if path.exists() else {})


def _read_json(path, default):
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else default


def _read_text(path):
    return path.read_text(encoding="utf-8") if path.exists() else ""


def _has_targets(art):
    return bool(_read_text(art / "formal/T_F.lean").strip()
                and _read_text(art / "nl/T_N.txt").strip())


def _read_cf(path):
    """Retain the declaration inventory alongside the curated items."""
    obj = _read_json(path, {"pin": {}, "available": [], "items": []})
    if isinstance(obj, list):
        obj = {"pin": {}, "available": obj, "items": []}
    if not isinstance(obj, dict):
        raise ValueError("C_F must be an inventory object or list")
    obj.setdefault("pin", {})
    obj.setdefault("available", obj.get("constants", []))
    obj.setdefault("items", [])
    return obj


def find_datapoints():
    found = []
    for root, dirs, _ in os.walk(REPO):
        dirs[:] = [d for d in dirs if d not in _SKIP_DIRS and not d.startswith(".")]
        if "artifacts" in dirs:
            found.append(Path(root) / "artifacts")
            dirs.remove("artifacts")
    return [{
        "path": str(art.parent.relative_to(REPO)),
        "label": _read_text(art / "label.txt").strip(),
        "has_targets": _has_targets(art),
        "done": _read_text(art / "done.txt").strip() == "true",
    } for art in sorted(found)]


def load_bundle(rel):
    """Read a variant's stored UTF-16 annotations and reading documents."""
    variant = (REPO / rel).resolve()
    path = str(variant.relative_to(REPO.resolve())) if variant.is_relative_to(REPO.resolve()) else str(variant)
    art = variant / "artifacts"
    return {
        "path": path, "format": read_format(variant), "has_targets": _has_targets(art),
        "T_F": _read_text(art / "formal/T_F.lean"),
        "T_N": _read_text(art / "nl/T_N.txt"),
        "version": _read_text(art / "formal/version.txt"),
        "C_F": _read_cf(art / "formal/C_F.json"),
        "S_F": _read_json(art / "formal/S_F.json", []),
        "S_N": _read_json(art / "nl/S_N.json", []),
        "C_N": _read_json(art / "nl/C_N.json", []),
        "I": _read_json(art / "nl/I.json", []),
        "R": _read_json(art / "relation/R.json", []),
        "lambda": _read_json(art / "relation/lambda.json", []),
        "label": _read_text(art / "label.txt").strip(),
        "done": _read_text(art / "done.txt").strip() == "true",
        **({"nl_context": _read_json(variant / "context/nl.json", [])}
           if (variant / "context/nl.json").exists() else {}),
    }


def _atomic_ref(ep):
    if not (isinstance(ep, list) and len(ep) == 2 and isinstance(ep[0], str)
            and ep[0] in ALL_KINDS and type(ep[1]) is int and ep[1] >= 0):
        raise ValueError(f"malformed endpoint {ep!r}")
    return tuple(ep)


def endpoint_parts(ep):
    """Return atomic reference tuples; BOT has none. Reject invalid groups."""
    if ep == BOT:
        return ()
    if not isinstance(ep, dict):
        return (_atomic_ref(ep),)
    parts = ep.get("parts")
    if set(ep) != {"parts"} or not isinstance(parts, list) or len(parts) < 2:
        raise ValueError("parts must contain at least two distinct atomic formal refs")
    refs = tuple(_atomic_ref(part) for part in parts)
    if any(kind not in FORMAL_KINDS for kind, _ in refs):
        raise ValueError("parts must contain only atomic formal refs")
    if len(set(refs)) != len(refs):
        raise ValueError("parts must contain distinct atomic formal refs")
    return refs


def link_rule_error(formal, nl, verdict, *, coverage="complete"):
    try:
        formal_refs, nl_refs = endpoint_parts(formal), endpoint_parts(nl)
    except ValueError as error:
        return str(error)
    if formal == BOT and nl == BOT:
        return "An empty-to-empty link is not allowed."
    if any(kind not in FORMAL_KINDS for kind, _ in formal_refs):
        return "Formal endpoints must be target spans or formal-context items."
    if isinstance(nl, dict) or any(kind not in NL_KINDS for kind, _ in nl_refs):
        return "NL endpoints must be target, context, or implicit spans."
    if type(verdict) is not int or verdict not in (0, 1):
        return "verdict must be 0 or 1"
    if coverage == "selective" and formal == BOT and nl != BOT and nl[0] in {"C_N", "I"} and verdict != 0:
        return "NL context or implicit assumptions linked to empty must be bad."
    return None


def _utf16_len(text):
    return len(text.encode("utf-16-le")) // 2


def _slice_utf16(text, start, end):
    encoded = text.encode("utf-16-le")
    if not 0 <= start <= end <= len(encoded) // 2:
        raise ValueError("interval is out of bounds")
    try:
        return encoded[2 * start:2 * end].decode("utf-16-le")
    except UnicodeDecodeError as error:
        raise ValueError("interval boundary splits a UTF-16 surrogate pair") from error


def interval_union(spans):
    """Canonical identity of a nonempty region, independent of partition/order."""
    if not isinstance(spans, list) or not spans:
        raise ValueError("expected a non-empty interval list")
    if any(not isinstance(iv, list) or len(iv) != 2
           or any(type(x) is not int for x in iv) or not 0 <= iv[0] < iv[1] for iv in spans):
        raise ValueError("expected nonempty [start, end] integer intervals")
    union = []
    for a, b in sorted(spans):
        if union and a <= union[-1][1]:
            union[-1][1] = max(union[-1][1], b)
        else:
            union.append([a, b])
    return tuple(map(tuple, union))


def _validate_spans(spans, text):
    """Validate every original interval, including boundaries hidden by unions."""
    if not isinstance(text, str):
        raise ValueError("expected source text")
    identity = interval_union(spans)
    encoded = text.encode("utf-16-le")
    length = len(encoded) // 2
    for a, b in spans:
        if b > length:
            raise ValueError(f"interval [{a}, {b}] out of bounds for UTF-16 len {length}")
        if any(offset < length and 0xDC <= encoded[2 * offset + 1] <= 0xDF
               for offset in (a, b)):
            raise ValueError(f"interval [{a}, {b}] splits a UTF-16 surrogate pair")
    return identity


def _source_name(source):
    if (not isinstance(source, str) or not source.startswith("context/")
            or "\\" in source or any(part in {"", ".", ".."} for part in source.split("/"))):
        raise ValueError("source must be a relative path inside the variant context directory")


def read_context_source(variant, source):
    _source_name(source)
    variant = (REPO / variant).resolve()
    root = (variant / "context").resolve()
    path = (variant / source).resolve()
    if not root.is_relative_to(variant) or not path.is_relative_to(root):
        raise ValueError("source must be inside the variant context directory")
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise ValueError(f"cannot read context source {source}: {error}") from error


def context_region_key(region):
    """Canonical per-document unions for C_N context or C_F source pieces."""
    pieces = region.get("pieces") if isinstance(region, dict) else None
    if not isinstance(pieces, list) or not pieces:
        raise ValueError("expected nonempty context pieces")
    field = "source" if isinstance(pieces[0], dict) and "source" in pieces[0] else "context"
    documents = {}
    for piece in pieces:
        if not isinstance(piece, dict) or set(piece) != {field, "spans"}:
            raise ValueError("invalid context piece")
        doc = piece[field]
        if field == "context" and (type(doc) is not int or doc < 0):
            raise ValueError("invalid context document")
        if field == "source":
            _source_name(doc)
        spans = interval_union(piece["spans"])
        documents.setdefault(doc, []).extend(map(list, spans))
    return tuple((doc, interval_union(spans)) for doc, spans in sorted(documents.items()))


def region_errors(data):
    """Validate target and context regions, including exact selected excerpts."""
    profile = bundle_format(data)
    unique = profile["coverage"] == "selective"
    errors = []
    for kind, target in (("S_F", "T_F"), ("S_N", "T_N")):
        seen = {}
        for i, spans in enumerate(data.get(kind, [])):
            try:
                identity = _validate_spans(spans, data[target])
                if unique and identity in seen:
                    errors.append(f"{kind}[{i}] duplicates {kind}[{seen[identity]}]; reuse that endpoint")
                else:
                    seen[identity] = i
            except ValueError as error:
                errors.append(f"{kind}[{i}]: {error}")
    source_texts = {}
    for kind, items in (("C_N", data.get("C_N", [])), ("C_F", data.get("C_F", {}).get("items", []))):
        seen = {}
        for i, item in enumerate(items):
            if not isinstance(item, dict) or "pieces" not in item:
                continue
            try:
                identity = context_region_key(item)
                if identity in seen:
                    errors.append(f"{kind}[{i}] duplicates {kind}[{seen[identity]}]; reuse that endpoint")
                else:
                    seen[identity] = i
                snippets = []
                for doc, spans in identity:
                    if kind == "C_N":
                        documents = data.get("nl_context", [])
                        if type(doc) is not int or not 0 <= doc < len(documents):
                            raise ValueError(f"invalid context document: {doc!r}")
                        text = documents[doc].get("text") if isinstance(documents[doc], dict) else None
                        field = "context"
                    else:
                        if not isinstance(doc, str):
                            raise ValueError("formal context pieces require source paths")
                        if not isinstance(data.get("path"), str) or not data["path"]:
                            raise ValueError("a variant path is required to resolve formal context pieces")
                        if doc not in source_texts:
                            source_texts[doc] = read_context_source(data["path"], doc)
                        text = source_texts[doc]
                        field = "source"
                    for piece in item["pieces"]:
                        if piece[field] == doc:
                            _validate_spans(piece["spans"], text)
                    snippets.extend(_slice_utf16(text, a, b) for a, b in spans)
                field, separator = ("text", " … ") if kind == "C_N" else ("signature", "\n…\n")
                if item.get(field) != separator.join(snippets):
                    errors.append(f"{kind}[{i}] {field} does not match its selected context pieces")
            except ValueError as error:
                errors.append(f"{kind}[{i}]: {error}")
    if unique:
        seen = {}
        for i, text in enumerate(data.get("I", [])):
            if not isinstance(text, str):
                errors.append(f"I[{i}]: expected a whole assumption string")
            elif text in seen:
                errors.append(f"I[{i}] duplicates I[{seen[text]}]; reuse that endpoint")
            else:
                seen[text] = i
    return errors
