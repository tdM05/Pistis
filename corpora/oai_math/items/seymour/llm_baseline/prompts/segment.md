Split this text into consecutive parts covering all of it. Label each part with one of: {{LABELS}}
Use `commentary` only if you are certain there is no other appropriate label and use `organizer-section` if you are unsure, and it is one of the available labels.

TEXT:
{{NL}}

For each part, give where it BEGINS as two verbatim strings:
- `target`: the exact text (copied verbatim from above) at the start of the part.
- `context`: a LARGER verbatim substring of the text above that contains `target` exactly once, so its location is unambiguous.
Copy both exactly — same characters, spacing, and symbols; do not normalize or reformat.

Reply ONLY with a JSON array: [{"label": "<one of the labels>", "target": "<verbatim start of the part>", "context": "<larger verbatim window containing target>"}]
