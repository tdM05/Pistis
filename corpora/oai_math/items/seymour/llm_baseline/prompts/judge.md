Is this {{LABEL}} from a math paper faithfully formalized in the Lean below?

TEXT:
{{NL}}

LEAN:
{{LEAN}}

A SPAN is {"file","target","context"}: `file` is one of the Lean files above (the name shown after `----- FILE:`), `target` is an exact verbatim Lean substring from that file, and `context` is a LARGER verbatim substring of the SAME file that contains `target` exactly once (so it locates unambiguously). A single symbol (e.g. `=`) is a valid `target` — use `context` to pin which occurrence. Copy both verbatim (same characters, spacing, symbols). Add `"approx": true` when the span is only an ANCHOR for where something SHOULD be, not a real counterpart.

`lean_spans` = where this TEXT maps in the Lean. If it is formalized, give the exact span(s). If NOTHING in the Lean corresponds, give exactly ONE approx anchor span marking where it should be.

`reason` = a JSON array with ONE entry per DISTINCT faithfulness error. Each entry is {"text","file","target","context","approx"}: `text` is exactly one sentence (one reason — make it a long single sentence if it is truly one reason, but never merge two reasons), and the span points to the offending Lean fragment, or an approx anchor marking where a missing thing belongs. If the TEXT is faithful, `reason` is [].

Reply ONLY with JSON: {"lean_spans": [{"file":"...","target":"...","context":"...","approx":false}, ...], "verdict": "faithful" | "unfaithful", "reason": [{"text":"...","file":"...","target":"...","context":"...","approx":false}, ...]}
