You are given the natural-language text of a mathematics paper and its Lean 4
formalization. Identify any faithfulness issues between the natural-language text
and the Lean formalization.

The natural-language text is shown as numbered lines. Each line begins with an
anchor `@N|` where N is the absolute character offset of the first character
after the `|`. The anchors are NOT part of the text; use them only to locate.

Output ONLY a JSON array (no prose, no markdown fences). Each element is one issue:

{
  "nl_anchor": <the integer N of the @N| line where the quoted text BEGINS>,
  "nl_quote": "<EXACT verbatim substring of that line (NOT including the @N| anchor) that the issue is about>",
  "lean_file": "<the Lean file name, e.g. MaxSupportKernel.lean>",
  "lean_quote": "<EXACT verbatim substring of that Lean file the issue is about>",
  "issue": "<one or two sentences describing the faithfulness discrepancy>"
}

Pinpointing rules (read carefully):
- `nl_quote` MUST be copied character-for-character from exactly ONE line — the
  line whose anchor you put in `nl_anchor`. Keep it short but long enough to be
  unique within that line. Do NOT include the `@N|` prefix in the quote.
- `lean_quote` MUST be copied character-for-character from `lean_file`.
- If something in the text is simply ABSENT from the Lean (no counterpart), set
  `lean_file` to the closest relevant file and `lean_quote` to "".

If there are no faithfulness issues, output [].

CRITICAL OUTPUT CONTRACT: Your ENTIRE response must be a single JSON array and
NOTHING else. Do NOT think out loud, do NOT explain your reasoning, do NOT write
any prose before or after. The first character of your response must be `[` and
the last must be `]`. If you have no findings, respond with exactly `[]`.

=== NATURAL-LANGUAGE TEXT (anchored lines) ===
{{NL}}

=== LEAN FORMALIZATION ===
{{LEAN}}
