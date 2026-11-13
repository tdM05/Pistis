# Plan: Lean pane highlighting = 1-to-1 mirror of the PDF pane

## Principle
The Lean pane must behave EXACTLY like the PDF pane. NL boxes map to Lean spans;
whatever the current level + its direct children are on the NL side, we persistently
show those boxes' Lean spans — in the SAME style as the PDF (outline/ring, not solid
fill). The only difference between the two panes is the coordinate mapping:
- PDF: a char range → page run rectangles (`charRuns`), drawn into `pageEls[].hl`.
- Lean: a char range → `.lean-src` line rectangles (`getClientRects`), drawn into `#leanCode`.
Everything else — WHICH boxes get painted and HOW they look — is identical.

## The reference (PDF side), to be mirrored verbatim
- `focusView()` → `{level, children}`: the current level node + its direct children.
- `paintHighlights()`:
  0. (optional later) link dependents: `{dep:true}`.
  1. the level node itself → `drawRange(..., boxHex(level.id), {outline:true})`.
  2. its direct children → segmented by overlap points, each segment
     `drawRange(s,e, blendHex(coverIds), {sel: selId∈cover})`.
- `drawRange(s,e,color,opts)` style, to copy EXACTLY:
  - `opts.outline` → background `rgba(110,110,110,0.28)` (grey), no own-color fill.
  - `opts.dep`     → striped gradient.
  - else           → `background = color+'55'`.
  - `WIREFRAME`    → inset 1px ring (`color+'cc'`, or grey for outline).
  - `opts.sel`     → inset 2px ring `SEL_OUTLINE+'cc'` (blue selection).

## What to implement
1. `paintLeanHighlights()` = structural copy of `paintHighlights()`:
   - uses the SAME `focusView()`.
   - paints the level node with `{outline:true}` and the direct children segmented by
     overlap, each `{sel: selId∈cover}` — using Lean spans (`leanSpans(n)`) instead of
     `pieces(n)`.
   - PERSISTENT: this is always shown for the current level (not flash-only).
2. `paintLeanRange(s,e,color,opts)` = structural copy of `drawRange(s,e,color,opts)`:
   - identical `opts` handling (`outline`/`dep`/`sel`/`WIREFRAME`) so the LOOK matches.
   - only the geometry (char→line rects) differs.
3. On top of the persistent view, the transient interactions stay:
   - click a FOL token → `flashLean` paints a transient purple (or red if the box is
     an error/∅) flash on its Lean span.
   - click Lean text → `leanSelectAt` → `selectBox` (blue selection ring, via the
     `{sel}` path in the persistent repaint).

## Discipline (why this time differs)
- Do NOT write parallel styling choices. `paintLeanRange`'s opts-branch must be
  character-identical to `drawRange`'s opts-branch (same backgrounds, same rings).
- Do NOT remove the persistent level-view. It is required, same as the PDF.
- The ONLY allowed divergence from the PDF functions is the char→rectangle mapping.
- Verify by diffing the opts-handling block of `paintLeanRange` against `drawRange`;
  they must match line-for-line except the rect source.

## Known prior failures (do not repeat)
- Drew solid `color+'55'` fills while removing the ring → looked like solid blue.
- Deleted the persistent level-view entirely → nothing showed.
- Invented a flash-only Lean view → diverged from the PDF.
