#!/usr/bin/env python3
"""Check UTF-16 regions and labeled mappings.

Complete coverage requires every non-whitespace target character and every
comparison vertex to have coverage. Selective coverage permits unselected
target text and unlinked formal context reading items.
Absent artifacts/format.json metadata means complete coverage.

Exit status: 0 when there are no errors, 1 otherwise.
Usage: python src/check_coverage.py [PATH ...]
"""
from __future__ import annotations

import sys

from alignment_data import (
    FORMAL_KINDS, NL_KINDS, _slice_utf16, _utf16_len,
    bundle_format, endpoint_parts, find_datapoints, link_rule_error,
    load_bundle, region_errors,
)


def _uncovered_runs(text, spans):
    """Maximal UTF-16 intervals outside all validated target regions."""
    n = _utf16_len(text)
    covered = bytearray(n)
    for span in spans:
        for a, b in span:
            covered[a:b] = b"\1" * (b - a)
    runs, i = [], 0
    while i < n:
        if covered[i]:
            i += 1
            continue
        j = i + 1
        while j < n and not covered[j]:
            j += 1
        runs.append((i, j))
        i = j
    return runs


def _lens(data):
    return {**{kind: len(data[kind]) for kind in ("S_F", "S_N", "C_N", "I")},
            "C_F": len(data["C_F"].get("items", []))}


def _check_endpoint(ep, side_kinds, lengths, errors, where):
    try:
        parts = endpoint_parts(ep)
    except ValueError as error:
        errors.append(f"{where}: {error}")
        return set()
    if isinstance(ep, dict) and side_kinds != FORMAL_KINDS:
        errors.append(f"{where}: parts are only valid on the formal side")
        return set()
    refs = set()
    for kind, index in parts:
        if kind not in side_kinds:
            errors.append(f"{where}: {kind} is not valid on this side ({sorted(side_kinds)})")
        elif index >= lengths[kind]:
            errors.append(f"{where}: {kind}[{index}] out of range (have {lengths[kind]})")
        else:
            refs.add((kind, index))
    return refs


def _freeze(ep):
    """Hashable edge identity; group order does not change the selected refs."""
    if isinstance(ep, dict):
        if set(ep) == {"parts"} and isinstance(ep["parts"], list):
            return ("parts", tuple(sorted((_freeze(part) for part in ep["parts"]), key=repr)))
        return tuple((key, _freeze(value)) for key, value in sorted(ep.items()))
    if isinstance(ep, list):
        return tuple(map(_freeze, ep))
    return ep


def _check_relation(data, errors):
    lengths = _lens(data)
    referenced = set()
    r_edges, l_edges = [], []
    for i, edge in enumerate(data["R"]):
        if not isinstance(edge, list) or len(edge) != 2:
            errors.append(f"R[{i}] is not a [formal, nl] pair: {edge!r}")
            continue
        formal, nl = edge
        if formal == "⊥" and nl == "⊥":
            errors.append(f"R[{i}] maps ⊥ to ⊥ (meaningless)")
        referenced.update(_check_endpoint(formal, FORMAL_KINDS, lengths, errors, f"R[{i}].formal"))
        referenced.update(_check_endpoint(nl, NL_KINDS, lengths, errors, f"R[{i}].nl"))
        r_edges.append(_freeze(edge))
    for i, item in enumerate(data["lambda"]):
        if not isinstance(item, list) or len(item) != 2:
            errors.append(f"lambda[{i}] is not [edge, [verdict, reason]]: {item!r}")
            continue
        edge, verdict = item
        if not (isinstance(verdict, list) and len(verdict) == 2
                and type(verdict[0]) is int and verdict[0] in (0, 1) and isinstance(verdict[1], str)):
            errors.append(f"lambda[{i}] verdict must be [0|1, reason]: {verdict!r}")
        if not isinstance(edge, list) or len(edge) != 2:
            errors.append(f"lambda[{i}] edge is not a [formal, nl] pair: {edge!r}")
            continue
        if isinstance(verdict, list) and len(verdict) == 2:
            error = link_rule_error(*edge, verdict[0], coverage=bundle_format(data)["coverage"])
            if error:
                errors.append(f"lambda[{i}]: {error}")
        l_edges.append(_freeze(edge))
    if sorted(r_edges, key=repr) != sorted(l_edges, key=repr):
        errors.append(f"R and lambda cover different edges (|R|={len(r_edges)}, |lambda|={len(l_edges)})")
    return referenced


def _report_side(tag, text, spans, referenced, errors, *, coverage):
    if coverage == "complete":
        for a, b in _uncovered_runs(text, spans):
            chunk = _slice_utf16(text, a, b)
            if chunk.strip():
                errors.append(f"{tag}: chars [{a}, {b}) not covered by any span: {chunk!r}")
    kind = "S_F" if tag == "T_F" else "S_N"
    for i, span in enumerate(spans):
        if (kind, i) not in referenced:
            fragment = " … ".join(_slice_utf16(text, a, b) for a, b in span)
            errors.append(f"{kind}[{i}] has no edge -- map it, or add a ⊥ edge: {fragment!r}")


def _check_context_cover(data, referenced, errors):
    selective = bundle_format(data)["coverage"] == "selective"
    for i, item in enumerate([] if selective else data["C_F"].get("items", [])):
        if ("C_F", i) not in referenced:
            name = item.get("name", "") if isinstance(item, dict) else item
            errors.append(f"C_F[{i}] has no edge -- link it or add a ⊥ edge: {name!r}")
    for i, item in enumerate(data["C_N"]):
        if ("C_N", i) not in referenced:
            desc = item.get("text", "") if isinstance(item, dict) else item
            errors.append(f"C_N[{i}] has no edge -- link it or add a ⊥ edge: {desc!r}")
    for i, item in enumerate(data["I"]):
        if ("I", i) not in referenced:
            errors.append(f"I[{i}] has no edge -- link it or add a ⊥ edge: {item!r}")


def check_bundle(data, *, finishing=True):
    """Return (errors, notes) for a bundle, including targets and variant path.

    Structural checks always apply. Drafts (finishing=False) may have missing
    edge coverage and text gaps. Completed annotations must satisfy their
    coverage profile.
    """
    try:
        profile = bundle_format(data)
    except ValueError as error:
        return [str(error)], []
    errors, notes = [], []
    for field in ("T_F", "T_N"):
        if not isinstance(data.get(field), str):
            errors.append(f"{field}: expected target text")
    for field in ("S_F", "S_N", "C_N", "I", "R", "lambda"):
        if not isinstance(data.get(field), list):
            errors.append(f"{field}: expected a list")
    if "nl_context" in data and not isinstance(data["nl_context"], list):
        errors.append("nl_context: expected a list")
    if not isinstance(data.get("C_F"), dict) or not isinstance(data["C_F"].get("items", []), list):
        errors.append("C_F: expected an object with an items list")
    if errors:
        return errors, notes
    errors.extend(region_errors(data))
    if errors:
        return errors, notes
    referenced = _check_relation(data, errors)
    if finishing:
        for target, kind in (("T_F", "S_F"), ("T_N", "S_N")):
            _report_side(target, data[target], data[kind], referenced, errors,
                         coverage=profile["coverage"])
        _check_context_cover(data, referenced, errors)
    return errors, notes


def check_datapoint(rel):
    try:
        data = load_bundle(rel)
    except (ValueError, OSError) as error:
        return [str(error)], []
    if not data["has_targets"]:
        return [], []
    return check_bundle(data)


def main(argv):
    paths = [arg for arg in argv if not arg.startswith("-")]
    if not paths:
        paths = [point["path"] for point in find_datapoints()]
    n_errors = n_notes = 0
    for rel in paths:
        errors, notes = check_datapoint(rel)
        print(f"[{'FAIL' if errors else 'ok'}] {rel}")
        for error in errors:
            print(f"    ERROR  {error}")
        for note in notes:
            print(f"    note   {note}")
        n_errors += len(errors)
        n_notes += len(notes)
    print(f"\n{len(paths)} datapoint(s): {n_errors} error(s), {n_notes} note(s)")
    return 1 if n_errors else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
