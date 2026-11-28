Is this {{LABEL}} from a math paper faithfully formalized in the Lean below?

TEXT:
{{NL}}

LEAN:
{{LEAN}}

`lean_map` entries must be EXACT declaration names copied verbatim from the Lean above (nothing invented).

Reply ONLY with JSON: {"lean_map": [<exact decl name(s) from the Lean, or [] if none>], "verdict": "faithful" | "unfaithful", "reason": [<one-sentence reason>, ...]}

`reason` is a JSON array of strings. If unfaithful, list each DISTINCT faithfulness error as its own entry; each entry must be exactly one sentence (make it a long single sentence if it is truly one reason, but never combine two separate reasons into one entry). If faithful, `reason` must be [] (empty).
