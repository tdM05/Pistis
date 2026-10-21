import Lean

/-!
# Pistis segmentation / faithfulness annotations

This module makes the natural-language → Lean *sentence mapping* a first-class proof object.
It is **domain-agnostic**: nothing here depends on any particular theory (geometry, algebra,
analysis, …) or on any solver. The tactics are plain Lean-meta code that emit an ordinary
`have` and record a metadata tuple; the *oracle* that discharges each step is the human (or an
LLM), not a tactic in this file.

A proof step that realizes one natural-language sentence is written with `pistis_segment`
instead of a bare `have`. It behaves exactly like `have name : type := by tac` (so the proof
term, local context, and any solver query are unchanged) but additionally records, into a
persistent environment extension, the tuple

    (locator, source-text, lean-type, have-name, source-position, module, line, kind)

Faithfulness *checking* (criterion 1: concatenate the recorded sentence texts and compare to the
canonical source) is done OUTSIDE Lean by a separate script that reads these annotations. This
module only RECORDS them.
-/

open Lean Elab Tactic Meta

namespace Pistis

/-- One recorded faithfulness annotation: a source sentence and the Lean step realizing it. -/
structure SegmentEntry where
  /-- Source-anchored locator, e.g. `"8.1.2"` = problem 8, step 1, sentence 2. -/
  loc  : String
  /-- The verbatim source sentence (the thing concatenation must recover). -/
  text : String
  /-- Surface syntax of the realizing step's type (for the human review table).
  Empty for `structural` entries, which emit no `have`. -/
  type : String
  /-- The `have` name introduced by the step, e.g. `"step8"`. Empty for `structural` entries. -/
  name : String
  /-- Source position `"line:col"` of the annotation. -/
  pos  : String
  /-- Module the annotation occurred in, e.g. `"ProofNet.Artin_10_2_4"`. Used by the external
  checker to associate this sentence's block with the module. -/
  mod  : String
  /-- Source line of the annotation (integer). -/
  line : Nat
  /-- `"logical"` = a real proof step (`pistis_segment`, emits a `have`); `"assumption"` = a
  premise a segment CONSUMES rather than asserts (`pistis_assumption`, also emits a `have`, with
  `loc` equal to the consuming segment's — several assumptions may share one `loc`); `"structural"`
  = enunciation / "we claim that" / QED boilerplate (`pistis_intro` / `pistis_conclude` /
  `pistis_wts`) that contributes its text to the criterion-1 concatenation but is NOT a logical
  step — it emits no `have`. -/
  kind : String
  deriving Inhabited, Repr

/-- Persistent env extension storing all `SegmentEntry`s. Entries from imported modules are
folded in, so a reader sees the current module plus its transitive imports.
(Shape follows Mathlib's `Mathlib/Tactic/Hint.lean`.)

`asyncMode := .sync`: our tactics record INTO this extension from inside theorem-body elaboration,
which Lean 4.28 runs on an async environment branch. The default `.mainOnly` panics when modified off
the main branch; `.sync` accumulates those modifications into the checked environment (blocking rather
than discarding), so every recorded entry reliably reaches the compiled `.olean` for the faithfulness
checker to read. (`.local` would silently discard off-main-branch entries — fatal here.) -/
initialize segmentExt :
    SimplePersistentEnvExtension SegmentEntry (List SegmentEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
    asyncMode := .sync
  }

/-- Current annotation's location: `(pos "line:col", module string, line number)`. -/
private def refLoc : TacticM (String × String × Nat) := do
  let fileMap ← getFileMap
  let modName := (← getMainModule).toString
  return match (← getRef).getPos? with
    | some p => let lc := fileMap.toPosition p; (s!"{lc.line}:{lc.column}", modName, lc.line)
    | none   => ("?", modName, 0)

/-- `pistis_segment "loc" "source text" (name : type) := by tac`

Realizes one source sentence. Elaborates to `have name : type := by tac` (identical proof term /
context to a plain `have`) and records a `logical` annotation into `segmentExt`. -/
syntax (name := pistisSegment)
  "pistis_segment " str str "(" ident " : " term ")" ":=" "by " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| pistis_segment $loc:str $txt:str ($nm:ident : $ty:term) := by $tac) => do
    let (posStr, modName, lineNo) ← refLoc
    -- Surface syntax of the type (verbatim slice when available).
    let typeStr := (ty.raw.reprint).getD (toString ty)
    modifyEnv fun env => segmentExt.addEntry env {
      loc  := loc.getString
      text := txt.getString
      type := typeStr
      name := nm.getId.toString
      pos  := posStr
      mod  := modName
      line := lineNo
      kind := "logical" }
    -- Emit the real `have`; proof term and local context unchanged.
    evalTactic (← `(tactic| have $nm:ident : $ty := by $tac))

/-- `pistis_intro "loc" "source text"` and `pistis_conclude "loc" "source text"`

Record a *structural* source sentence — the enunciation preamble (placed right after the intro)
or the closing restatement + QED boilerplate (placed at the final step). These contribute their
text to the criterion-1 concatenation but are NOT logical steps: they emit no `have` (the tactic
is a `skip`), so the proof term and local context are unchanged. -/
syntax (name := pistisIntro)
  "pistis_intro " str str : tactic
syntax (name := pistisConclude)
  "pistis_conclude " str str : tactic

/-- `pistis_wts "loc" "source text"`

Record a *structural* mid-proof "we claim / it suffices to show …" (what-to-show) sentence. Like
the intro/conclude tactics it emits no `have` (proof term / context unchanged) and only
contributes its text to the criterion-1 concatenation — but unlike them it is permitted MID-proof.
A "we claim X" announces the goal; it is NOT an assertion that X is already proven, so it carries
no claim. The real content X is established by the following sentences and assembled by the
trailing step. -/
syntax (name := pistisWts)
  "pistis_wts " str str : tactic

/-- Shared recorder for the structural tactics. -/
private def recordStructural (loc txt : TSyntax `str) : TacticM Unit := do
  let (posStr, modName, lineNo) ← refLoc
  modifyEnv fun env => segmentExt.addEntry env {
    loc  := loc.getString
    text := txt.getString
    type := ""
    name := ""
    pos  := posStr
    mod  := modName
    line := lineNo
    kind := "structural" }
  -- No tactic is emitted: this is a pure annotation, valid whether or not goals remain (it may
  -- follow the final step). Recording only — proof term and local context are untouched.
  pure ()

elab_rules : tactic
  | `(tactic| pistis_intro $loc:str $txt:str)    => recordStructural loc txt
  | `(tactic| pistis_conclude $loc:str $txt:str) => recordStructural loc txt
  | `(tactic| pistis_wts $loc:str $txt:str)      => recordStructural loc txt

/-- `pistis_assumption "loc" "source text" (name : type) := by tac`

A premise a segment CONSUMES rather than asserts (the paper's `assumps(sᵢ)`), as opposed to
`pistis_segment`'s `assert(sᵢ)`. Same shape and elaboration as `pistis_segment` — expands to
`have name : type := by tac`, so the proof term and local context are unchanged — with two
differences recorded in the tuple: `kind := "assumption"`, and `loc` is the SAME locator as the
`pistis_segment` that consumes it (several assumptions may share one `loc`; they are ordered by
source position within it). Sharing `pistis_segment`'s exact shape — rather than a bare comment —
is what lets a reader (or the UI) hover/open an assumption exactly like a segment, and what lets the
map stage's `lake env lean` elaborate its `type` immediately instead of deferring that check. -/
syntax (name := pistisAssumption)
  "pistis_assumption " str str "(" ident " : " term ")" ":=" "by " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| pistis_assumption $loc:str $txt:str ($nm:ident : $ty:term) := by $tac) => do
    let (posStr, modName, lineNo) ← refLoc
    let typeStr := (ty.raw.reprint).getD (toString ty)
    modifyEnv fun env => segmentExt.addEntry env {
      loc  := loc.getString
      text := txt.getString
      type := typeStr
      name := nm.getId.toString
      pos  := posStr
      mod  := modName
      line := lineNo
      kind := "assumption" }
    -- Emit the real `have`; proof term and local context unchanged.
    evalTactic (← `(tactic| have $nm:ident : $ty := by $tac))

end Pistis
