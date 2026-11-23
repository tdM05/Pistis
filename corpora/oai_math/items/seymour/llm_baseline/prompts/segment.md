You are given a region of the natural-language text of a mathematics paper, shown
as numbered lines `@OFFSET|text` (the `@OFFSET|` prefix is a reading aid, NOT part
of the text). Split this region into its TOP-LEVEL parts, in reading order.

Label each part with ONE of these labels: {{LABELS}}
  - organizer-section : a titled/numbered structural block or heading-led section
    (e.g. the title block, the Abstract, "1 Introduction", "2 ...", References).
  - commentary        : free prose / motivation with no formal statement.
  - definition        : a mathematical definition (introduces notation/an object).
  - theorem           : a theorem / lemma / proposition / corollary statement (with
    or without its proof as part of the same block).

Output ONLY a JSON array (first char `[`, last char `]`, no prose). Each element:

{
  "label": "<one of the labels above>",
  "start_text": "<the EXACT verbatim text at the START of this part, copied
     character-for-character from the lines (do NOT include the @OFFSET| prefix),
     about 4–12 words — enough to locate this part's beginning uniquely>"
}

Rules:
- The parts are in reading order and together COVER the whole region with no gaps.
- The FIRST part begins at the very start of the region.
- `start_text` must be an EXACT substring of the text so it can be found by search.
  Begin it at a natural boundary (a heading, the first word of a sentence).

=== TEXT REGION (anchored lines) ===
{{NL}}
