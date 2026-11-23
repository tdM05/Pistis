You are given a slice of the natural-language text of a mathematics paper, and a
list of the Lean 4 files that formalize (parts of) it.

Split the slice into its top-level parts, in reading order. A part is a
contiguous run of text that forms one unit (e.g. an abstract, an introduction
paragraph, a definition, a theorem statement, a proof, a remark, a section of
commentary). For each part decide whether it is FORMALIZED in Lean — i.e. it
states a definition / theorem / lemma / proof that has a counterpart among the
Lean files — or is non-formal prose (motivation, commentary, references).

The text is shown as numbered lines `@N|text` where N is the absolute character
offset of the first character after `|`. Use these offsets for the ranges.

Output ONLY a JSON array (no prose, no fences). Each element:

{
  "title": "<short label for this part>",
  "nl_anchor_start": <offset N of the first line of this part>,
  "nl_anchor_end": <offset N of the first line AFTER this part (or the end)>,
  "formalized": true | false,
  "lean_files": ["<file that most likely formalizes it>", ...]
}

Rules:
- The parts must cover the slice in order, non-overlapping.
- `lean_files` is [] when `formalized` is false, else the 1–3 most relevant files.

=== NATURAL-LANGUAGE SLICE (anchored lines) ===
{{NL}}

=== AVAILABLE LEAN FILES ===
{{LEANLIST}}
