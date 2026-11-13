// align_driver — ties the pieces together: given a FOL definition/theorem box id,
// extract its Lean decl, normalize, align, and return {alignment, findings}.
//
// Pure except for extract() (which shells to lean, cached). Shared by the CLI
// (inspect.js --align) and the server (/align endpoint for the UI).
import { readFileSync } from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import { normalize, peelBinders, peelTypeBinders, constNames } from './lean_normalize.js';
import { makeAligner } from './align.js';
import { extract } from './lean_extract/extract.js';
import { surface, locate, pretty } from './lean_spans.js';

const SEG_DIR = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');   // pdf_direct_segment/

// Align one FOL box (a definition or theorem) against its Lean decl.
//   core    : makeCore(schema) result
//   root    : the annotation ROOT
//   box     : the FOL box (must be in dict.decls)
//   chars   : the global CHARS string (for symbol slugs)
//   dict    : lean_dict.json  ({decls, symbols})
// Returns { ok, reason?, alignment?, findings?, leanDecl? }.
export function alignBox({ core, root, box, chars, dict }) {
  const C = core;
  // align works at the box that carries a Lean decl association. If `box` is
  // INSIDE such a box (e.g. a sub-formula), walk up to the nearest ancestor that
  // has one — so aligning from anywhere inside a definition aligns the definition.
  let target = box;
  while (target && !(dict.decls && dict.decls[target.id])) target = C.parentOf(root, target.id);
  if (!target) return { ok: false, reason: `no Lean decl associated with ${box.id} or any ancestor (add it to lean_dict.json → decls)` };
  box = target;
  const assoc = dict.decls[box.id];
  let raw; try { raw = extract({ decl: assoc.decl, srcFile: assoc.src }); }
  catch (e) { return { ok: false, reason: 'lean extract failed: ' + e.message }; }

  const concrete = C.labelConcrete(box.label);
  const symText = (x) => { const ps = C.pieces(x); if (!ps.length) return '∅'; return chars.slice(ps[0].start, ps[0].end).replace(/\s+/g, ' ').trim().replace(/ /g, '_'); };

  // Lean side: a `def` elaborates to `fun <inputs> => body`. Peel the lam-binders
  // (the inputs) to reach the body (which the FOL `body` slot aligns against).
  // For a theorem the value is a proof; we align the TYPE (the statement) instead.
  const normVal = raw.value && raw.value.kind ? normalize(raw.value) : null;
  const normType = normalize(raw.type);
  // the decl's input binders with the SET OF CONSTS in each binder's type, so the
  // aligner can VERIFY type-vs-prop discharges (e.g. `real` only if a binder's
  // type mentions `Real`). Pulled from the TYPE (which carries the binder types).
  const typeBinders = peelTypeBinders(raw.type).map((b) => ({ binder: b.binder, info: b.info, dom: b.dom, typeConsts: constNames(b.dom || {}) }));
  const A = makeAligner(C, dict.symbols || {}, symText, { binders: typeBinders, tuples: dict.tuples || {} });

  // attach SOURCE POSITIONS (from the parsed syntax tree, raw.binders) to the Expr
  // binders, so inputs↔binder-NAME and conditions↔binder-TYPE spans resolve to exact
  // source ranges. raw.binders is the full ordered source binder list (the `variable`
  // line(s) AND the signature); the elaborated Expr keeps only the binders the decl
  // actually uses (e.g. Fintypes dropped), a SUPERSET in the same relative order.
  // Reconcile by walking both in order, consuming a source binder when NAMES agree
  // (this only SKIPS dropped binders; order is still the model, not name-matching).
  // Shared by the definition and theorem paths.
  {
    const srcBuf = (() => { try { return readFileSync(path.join(SEG_DIR, deriveLeanRel(assoc)), 'utf8'); } catch (_) { return ''; } })();
    const b2c = srcBuf ? Buffer.from(srcBuf, 'utf8') : null;
    const nameOf = (r) => { if (!r || !b2c) return ''; return b2c.slice(r.start, r.stop).toString('utf8').replace(/[[\]{}()]/g, '').trim(); };
    const synB = raw.binders || [];
    let si = 0;
    for (const tb of typeBinders) {
      while (si < synB.length && nameOf(synB[si].name) !== tb.binder) si++;
      if (si < synB.length) { tb.synName = synB[si].name; tb.synType = synB[si].type; si++; }
    }
  }

  if (concrete === 'definition') {
    const { binders } = peelBinders(normVal || {});
    const lamInputs = binders.filter((b) => b.kind === 'lam');
    let leanBody = normVal; for (let i = 0; i < lamInputs.length; i++) leanBody = leanBody.body;
    const slot = (k) => (box.children || []).find((c) => c.label && c.label[0] === k);
    const bodyBox = slot('body');
    if (!bodyBox) return { ok: false, reason: 'definition has no body slot to align' };

    // The Lean decl is `def Name {I J} [insts] (T) (D) : Prop := body`. Each FOL
    // slot maps to a DIFFERENT part of it (see doc/align-todo.md):
    //   name       → the definiendum (decl name)
    //   inputs     → the binders (typeBinders: I J T D), matched BY NAME
    //   conditions → the binder TYPES (e.g. T⊆I×J ↔ `T : Set (I×J)`), by subject var
    //   body       → the peeled body, via the structural aligner (halts on mismatch)
    // (binder source positions were reconciled above — shared with the theorem path.)
    const children = [];
    children.push(alignName(slot('name'), assoc.decl));
    children.push(alignInputs(slot('inputs'), typeBinders));
    children.push(alignConditions(slot('conditions'), typeBinders));
    children.push(labelNode(bodyBox, A.align(bodyBox, leanBody), 'body'));

    const alignment = { fol: box.id, lean: null, leanNode: null, status: 'match', note: '', children };
    return finish(alignment, assoc, lamInputs, { leanBody, typeBinders, ranges: raw.ranges });
  }
  if (concrete === 'theorem') {
    // theorem = statement + proof. The STATEMENT mirrors a definition, so its slots
    // map to the SAME parts of the decl's signature:
    //   name       → the decl name
    //   inputs     → the binders (typeBinders), matched BY NAME
    //   conditions → the binder TYPES, by subject var
    //   conclusion → the decl's RESULT TYPE: normType with ALL its binders peeled
    // The difference from a def is only WHERE the body comes from: a def's body is the
    // VALUE (after :=); a theorem's conclusion is the TYPE (after the last : before :=).
    // The `proof` (the value) is OUT OF SCOPE for structural alignment (align-todo.md).
    const stmtBox = (box.children || []).find((c) => c.label && c.label[0] === 'statement');
    if (!stmtBox) return { ok: false, reason: 'theorem has no statement slot to align (expected a statement child with name/inputs/conditions/conclusion)' };
    const sslot = (k) => (stmtBox.children || []).find((c) => c.label && c.label[0] === k);
    const conclWrap = sslot('conclusion');
    if (!conclWrap) return { ok: false, reason: 'theorem statement has no conclusion slot to align' };
    // the conclusion wrapper holds ONE formula box — that is what aligns to Lean.
    const conclBox = (conclWrap.children || []).find((c) => C.isFormulaish(c)) || conclWrap;
    // Lean conclusion = the type with ALL binders peeled (used→forall, unused→arrow).
    let leanConcl = normType; for (let i = 0; i < typeBinders.length && leanConcl; i++) leanConcl = leanConcl.body;

    const children = [];
    children.push(alignName(sslot('name'), assoc.decl));
    children.push(alignInputs(sslot('inputs'), typeBinders));
    children.push(alignConditions(sslot('conditions'), typeBinders));
    children.push(labelNode(conclBox, A.align(conclBox, leanConcl), 'conclusion'));

    const alignment = { fol: box.id, lean: null, leanNode: null, status: 'match', note: '', children };
    return finish(alignment, assoc, [], { leanBody: leanConcl, typeBinders, ranges: raw.ranges });
  }
  // bare top-level `formula` box (no statement wrapper): align against the Lean TYPE.
  const alignment = A.align(box, normType);
  return finish(alignment, assoc, [], { leanBody: normType, typeBinders, ranges: raw.ranges });

  // ── slot aligners (definition) ────────────────────────────────────────────
  // wrap a sub-alignment produced by the structural aligner so it is tagged with
  // the FOL slot box it belongs to (keeps the slot visible in the report tree).
  function labelNode(folBox, sub, slotName) {
    // the wrapper is a structural grouping only; the real status/finding lives on
    // `sub` (the aligner's node). Keep the wrapper neutral so the finding is not
    // double-counted (wrapper + sub both carry the same fol id).
    return { fol: null, lean: null, leanNode: null, status: 'match', note: '', slot: slotName, children: [sub] };
  }
  // name ↔ definiendum: the `name` box maps to the decl's own name. The leanNode is
  // a synthetic const so the span walk locates the `def <Name>` occurrence.
  function alignName(nameBox, decl) {
    const leaf = decl.split('.').pop();
    if (!nameBox) return { fol: null, lean: leaf, leanNode: null, status: 'unmapped', note: `Lean defines '${leaf}' but NL has no name slot`, slot: 'name', children: [] };
    return { fol: nameBox.id, lean: leaf, leanNode: { t: 'const', name: leaf }, status: 'leaf', note: `name ↔ ${leaf}`, slot: 'name', children: [] };
  }
  // ONE ordered binder list. There is NO "object vs constraint" distinction in Lean —
  // each binder `(x : τ)` carries BOTH: its NAME x is an input, its TYPE τ is a
  // condition. So inputs and conditions both match POSITIONALLY against the SAME
  // ordered binder list (tbinders), by name and by type respectively.

  // inputs ↔ binder NAMES, positionally. Nth input ↔ name of Nth binder.
  function alignInputs(inputsBox, tbinders) {
    if (!inputsBox) return { fol: null, lean: null, leanNode: null, status: 'match', note: 'no inputs slot', slot: 'inputs', children: [] };
    const invars = (inputsBox.children || []).filter((c) => C.isVariable(c));
    const kids = []; const n = Math.max(invars.length, tbinders.length);
    for (let i = 0; i < n; i++) {
      const v = invars[i], tb = tbinders[i];
      if (v && tb) kids.push({ fol: v.id, lean: 'binder ' + tb.binder, leanNode: { t: 'var', name: tb.binder }, synPos: tb.synName, status: 'leaf', note: `input #${i + 1} ↔ binder ${tb.binder}`, children: [] });
      else if (v) kids.push({ fol: v.id, lean: '∅', leanNode: null, status: 'mismatch', note: `input #${i + 1} '${symText(v)}' maps to nothing — Lean has no binder at this position`, children: [] });
      else kids.push({ fol: null, lean: 'binder ' + tb.binder, leanNode: { t: 'var', name: tb.binder }, synPos: tb.synName, status: 'unmapped', note: `Lean binder #${i + 1} '${tb.binder}' has no input at this position`, children: [] });
    }
    const bad = kids.some((k) => k.status !== 'leaf');
    return { fol: inputsBox.id, lean: null, leanNode: null, status: bad ? 'mismatch' : 'match', note: '', slot: 'inputs', children: kids };
  }
  // conditions ↔ binder TYPES, positionally. The CONDITIONS are the types of every
  // binder whose type is NOT a universe (Type*/Sort* — those just declare a carrier
  // sort, which is not a condition in FOL). So `{I J : Type*}` are dropped, and e.g.
  // `[Fintype I] [Fintype J] (T : Set (I×J)) (D : Matrix I J ℝ)` give 4 conditions.
  // Nth NL condition ↔ type of the Nth non-sort binder.
  function alignConditions(condsBox, tbinders) {
    if (!condsBox) return { fol: null, lean: null, leanNode: null, status: 'match', note: 'no conditions slot', slot: 'conditions', children: [] };
    const conds = (condsBox.children || []).filter((c) => C.isFormulaish(c));
    const cbinders = tbinders.filter((tb) => !(tb.dom && tb.dom.t === 'sort'));   // drop universe/sort binders
    const kids = []; const n = Math.max(conds.length, cbinders.length);
    for (let i = 0; i < n; i++) {
      const cond = conds[i], tb = cbinders[i];
      if (cond && tb) kids.push({ fol: cond.id, lean: 'type of ' + tb.binder, leanNode: tb.dom || null, synPos: tb.synType, status: 'leaf', note: `condition #${i + 1} ↔ type of binder ${tb.binder}`, children: [] });
      else if (cond) kids.push({ fol: cond.id, lean: '∅', leanNode: null, status: 'mismatch', note: `condition #${i + 1} maps to nothing — Lean has no binder at this position (NL asserts a hypothesis the Lean statement does not)`, children: [] });
      else kids.push({ fol: null, lean: 'type of ' + tb.binder, leanNode: tb.dom || null, synPos: tb.synType, status: 'unmapped', note: `Lean binder #${i + 1} '${tb.binder}' type has no condition at this position`, children: [] });
    }
    const bad = kids.some((k) => k.status !== 'leaf');
    return { fol: condsBox.id, lean: null, leanNode: null, status: bad ? 'mismatch' : 'match', note: '', slot: 'conditions', children: kids };
  }

  function finish(alignment, assoc, lamInputs, extra = {}) {
    // NL text of a FOL box (its highlighted span) — so the report reads in words,
    // not box ids. Empty for implicit boxes.
    const nlText = (id) => { let b = id && C.find(root, id); if (!b) return '';
      // implicit boxes have no span → climb to the nearest spanned ancestor so the
      // report still reads in words (e.g. the containing clause).
      while (b && !(C.pieces(b).length)) b = C.parentOf(root, b.id);
      if (!b) return ''; const ps = C.pieces(b); return ps.length ? chars.slice(ps[0].start, ps[0].end).replace(/\s+/g, ' ').trim() : ''; };

    const spans = {};
    const leanRegions = [];   // (⊥,F) Lean-only judged regions (no FOL box)
    const pieceSpans = [];    // [start,end] of every mapped leaf piece (for gap tiling)
    const containmentErrors = [];   // mapped pieces whose Lean span is OUTSIDE the def span
    let declRegion = null;    // [lo,hi) the def's full Lean span (incl. variable line)
    let text = '', fileField = '', leanSource = '', leanLine = null;
    try {
      const abs = path.join(SEG_DIR, deriveLeanRel(assoc));
      text = readFileSync(abs, 'utf8');
      fileField = deriveLeanRel(assoc);
      // Lean gives source positions as UTF-8 BYTE offsets; JS string indices are
      // UTF-16 code units. Convert a byte offset → JS string index via the byte
      // length of the growing prefix (one pass, memoized by scanning).
      const byteBuf = Buffer.from(text, 'utf8');
      const byteToChar = (byteOff) => byteBuf.slice(0, byteOff).toString('utf8').length;
      const nameLeaf = assoc.decl.split('.').pop();
      // decl start: prefer the EXACT range Lean gives (extra.ranges, from
      // findDeclarationRanges? — 1-based line, 0-based col); fall back to a text
      // search for `def <name>`/`theorem <name>` only if Lean gave no range.
      const lineColToOffset = (ln, col) => { // ln 1-based, col 0-based → char offset
        let off = 0, line = 1; while (line < ln) { const nl = text.indexOf('\n', off); if (nl < 0) return text.length; off = nl + 1; line++; } return off + col; };
        const rg = extra.ranges;
      let declAt = rg && rg.declStart ? lineColToOffset(rg.declStart.line, rg.declStart.col) : -1;
      if (declAt < 0) { for (const kw of ['def ', 'theorem ', 'lemma ']) { const i = text.indexOf(kw + nameLeaf); if (i >= 0) { declAt = i; break; } } }
      const asgn = declAt >= 0 ? text.indexOf(':=', declAt) : text.indexOf(':=');
      // region boundaries within the source:
      //   [sigLo, sigHi)  = the signature (name + binders + result type), before :=
      //   [bodyLo, bodyHi)= the body, after :=
      const sigLo = declAt >= 0 ? declAt : 0;
      const sigHi = asgn >= 0 ? asgn : (declAt >= 0 ? text.indexOf('\n', declAt) : 0);
      let bodyLo = asgn >= 0 ? asgn + 2 : 0;
      let bodyHi = text.indexOf('\n\n', bodyLo); if (bodyHi < 0) bodyHi = text.length;
      const tnl = text.indexOf('\ntheorem', bodyLo); if (tnl >= 0 && tnl < bodyHi) bodyHi = tnl;
      // 1-based line of the decl. (leanSource — the displayed decl text — is set AFTER
      // the tiling below, to the full def span incl. the variable line.)
      if (declAt >= 0) { leanLine = text.slice(0, declAt).split('\n').length; }
      // which source region a slot's spans live in. name/inputs/conditions all live
      // in the SIGNATURE; body lives in the body region. The structural body walk
      // (via leanNode surfaces) locates within the body as before.
      const slotRegion = (slot) => (slot === 'body' || slot == null) ? [bodyLo, bodyHi] : [sigLo, sigHi];
      // walk: allocate a Lean span per node AND decorate the node with NL + Lean
      // text so the UI can render human-readable rows. `slot` threads down from the
      // nearest ancestor that declared one, choosing the source region to search in.
      const walk = (n, lo, hi, slot) => {
        const mySlot = n.slot || slot;
        if (n.slot) { const [rlo, rhi] = slotRegion(n.slot); lo = rlo; hi = rhi; }
        let mySpan = null;
        // locate target, in priority:
        //  - synPos : a REAL source range from Lean's parse tree (byte offsets) — an
        //             input → its binder NAME span, a condition → its binder TYPE
        //             span. Exact, no text search. Converted byte→char here.
        //  - else   : surface the elaborated leanNode and search for it in-region.
        let loc = null;
        if (n.synPos) { let a = byteToChar(n.synPos.start), b = byteToChar(n.synPos.stop);
          // trim a leading ": " on a type-ascription range so it points at the type
          while (a < b && (text[a] === ':' || text[a] === ' ')) a++;
          loc = { start: a, end: b }; }
        if (!loc) { const surf = n.leanNode ? surface(n.leanNode) : null; loc = surf ? locate(text, lo, hi, surf) : null; }
        if (loc) { mySpan = loc; if (n.fol) spans[n.fol] = { file: fileField, start: loc.start, end: loc.end }; }
        else if (n.fol && n.leanNode) spans[n.fol] = { file: fileField, start: lo, end: hi, approx: true };
        n.nl = nlText(n.fol);
        n.leanText = loc ? text.slice(loc.start, loc.end).replace(/\s+/g, ' ').trim() : (n.leanNode ? pretty(n.leanNode) : '');
        // VERDICT ON THE LINK. A judged node ALWAYS yields a link carrying the verdict:
        //  - leaf (ok)    → link to its Lean span, v:ok
        //  - mismatch     → notok link; to its Lean span if it has one, else a link to
        //                   NOTHING (none:true) when it maps to ∅ (no binder/counterpart
        //                   at this position). The verdict is a property of THIS link.
        // slot wrappers (inputs/conditions) carry NO link of their own — they DERIVE
        // by rolling up their children. Every other judged node (leaf, or a mismatch
        // like the body ∧ whose children are only informational) gets a link+verdict.
        const isWrapper = n.slot === 'inputs' || n.slot === 'conditions';
        if (n.fol && !isWrapper) {
          if (n.status === 'mismatch') {
            if (!spans[n.fol]) spans[n.fol] = { none: true };
            spans[n.fol].v = 'notok'; spans[n.fol].why = humanFinding(n); spans[n.fol].cmp = n.leanText || '(nothing)'; spans[n.fol].path = labelPath(n.fol);
          } else if (n.status === 'leaf' && spans[n.fol]) { spans[n.fol].v = 'ok'; }
        }
        // (⊥, F): a Lean-only piece (fol:null, has a source span) — a compiled binder
        // NL never covers. It's a judged Lean REGION, not keyed to any FOL box, so it
        // goes in its own list. Its verdict: notok (NL omits a piece the Lean
        // statement has). The UI paints these as notok Lean regions.
        if (!n.fol && loc && n.status === 'unmapped') {
          leanRegions.push({ file: fileField, start: loc.start, end: loc.end, v: 'notok', why: n.note, lean: n.leanText });
        }
        // every piece span contributes to the decl's coverage — used after the walk
        // to compute the UNCOVERED gaps (scaffolding: def/:/:=/Prop). Read from
        // spans[fol] (set above, incl. the approx BODY span) so the body region isn't
        // mistaken for an uncovered gap; plus any located non-fol region (⊥ pieces).
        if (n.fol && spans[n.fol] && spans[n.fol].start != null) pieceSpans.push([spans[n.fol].start, spans[n.fol].end]);
        else if (loc) pieceSpans.push([loc.start, loc.end]);
        const clo = mySpan ? mySpan.start : lo, chi = mySpan ? mySpan.end : hi;
        (n.children || []).forEach((c) => walk(c, clo, chi, mySlot));
      };
      walk(alignment, bodyLo, bodyHi, null);
      // COMPLETE THE TILING. The def's Lean span is the WHOLE region from the start of
      // the line of its earliest mapped piece (so a `variable {I J …}` line whose
      // binders the def pulls in is included) through the body end. Every char in that
      // region is either in a mapped piece or in a GAP (scaffolding: `variable`, `def`,
      // `(`, `:`, `)`, `: Prop`, `:=`, whitespace) → emitted as a bot_ok region. (Extra
      // binders are bot_notok above.) So the def is fully tiled, every span ok/notok.
      {
        const merged = pieceSpans.slice().filter(([a, b]) => b > a).sort((x, y) => x[0] - y[0]);
        // region start = start of the line containing the earliest mapped piece (else
        // the decl start) — this pulls in the `variable` line(s) the def depends on.
        const firstPiece = merged.length ? merged[0][0] : (declAt >= 0 ? declAt : sigLo);
        const lineStart = text.lastIndexOf('\n', firstPiece - 1) + 1;   // 0 if none
        declRegion = [lineStart, bodyHi];
        let cur = lineStart;
        const end = bodyHi;
        for (const [a, b] of merged) {
          if (a > cur) leanRegions.push({ file: fileField, start: cur, end: a, v: 'ok', why: 'formal scaffolding (no NL counterpart)', lean: text.slice(cur, a).replace(/\s+/g, ' ') });
          cur = Math.max(cur, b);
        }
        if (cur < end) leanRegions.push({ file: fileField, start: cur, end, v: 'ok', why: 'formal scaffolding (no NL counterpart)', lean: text.slice(cur, end).replace(/\s+/g, ' ') });
        // displayed decl text = the full def span (variable line → body)
        leanSource = text.slice(lineStart, bodyHi).trim();
      }
      // CONTAINMENT ENFORCEMENT: every mapped Lean piece span MUST lie within the
      // def's Lean span [declRegion]. A piece outside it means the alignment linked an
      // NL box to Lean text the def doesn't even cover — a hard error, surfaced as a
      // finding (this is the check that was missing when I/J mapped to a line outside
      // the def span).
      if (declRegion) {
        const [rlo, rhi] = declRegion;
        for (const id in spans) { const sp = spans[id]; if (sp.start == null) continue;
          if (sp.start < rlo || sp.end > rhi) containmentErrors.push({ fol: id, start: sp.start, end: sp.end, text: text.slice(sp.start, sp.end).replace(/\s+/g, ' ').trim() }); }
      }
    } catch (_) { /* best-effort */ }
    // the elaborated/compiled term the aligner actually walked (what it compares
    // against, not the surface text) — pretty-printed for display.
    const leanElaborated = extra.leanBody ? pretty(extra.leanBody) : '';

    // human-readable findings: only real problems (mismatch/unmapped). Each finding
    // carries the FOL object's FULL LABEL PATH, the Lean file path + span it was
    // compared against, the NL text, and the structural note.
    const findings = [];
    (function collect(n) {
      // a slot wrapper (inputs/conditions) carries no finding of its own — its
      // status just reflects its children; the real findings are on the children.
      const isSlotWrapper = n.slot === 'inputs' || n.slot === 'conditions';
      if ((n.status === 'mismatch' || n.status === 'unmapped') && !isSlotWrapper) {
        const sp = n.fol && spans[n.fol];
        const hasLoc = sp && sp.start != null;   // a ∅ (none) span has no position
        findings.push({
          fol: n.fol,
          path: labelPath(n.fol),
          nl: n.nl || '(implicit)',
          lean: n.leanText || n.lean,
          leanLoc: hasLoc ? `${sp.file}:${sp.start}-${sp.end}` : (fileField ? `${fileField}${leanLine ? ':' + leanLine : ''}` : ''),
          message: humanFinding(n),
        });
      }
      (n.children || []).forEach(collect);
    })(alignment);
    // CONTAINMENT violations → hard findings: an NL box linked to Lean text OUTSIDE
    // the def's own span. This must never happen; if it does, it's a real error.
    for (const e of containmentErrors) {
      findings.push({ fol: e.fol, path: labelPath(e.fol), nl: nlText(e.fol) || '(implicit)',
        lean: e.text, leanLoc: `${fileField}:${e.start}-${e.end}`,
        message: `CONTAINMENT ERROR: this maps to Lean text outside the declaration's span ('${e.text}') — a child's Lean span must lie within its parent's` });
    }
    return {
      ok: true, alignment, findings, spans, leanRegions,
      leanDecl: assoc.decl,
      leanFile: fileField, leanLine, leanSource, leanElaborated,
      leanInputs: lamInputs.map((b) => ({ binder: b.binder, info: b.info })),
    };
  }
  // the FULL concrete label path of a FOL box, e.g.
  // "body.formula.compound-formula.connective.conjunction". Generic over all labels
  // (no per-symbol hardcoding) — this is how a finding names the object it concerns.
  function labelPath(id) {
    const b = id && C.find(root, id);
    return b && b.label ? b.label.join('.') : '';
  }
  // turn an alignment node's internal note into a plain-language problem message.
  // The object is named by its FULL LABEL PATH in a SEPARATE field (`path`), so the
  // message itself does NOT repeat it. Derives the FOL kind from the label path's
  // last component (generic, not a hardcoded symbol table) + the Lean kind.
  function humanFinding(n) {
    const obj = labelPath(n.fol);
    const kind = obj ? obj.split('.').pop() : (n.note.match(/FOL (\w+)/) || [])[1] || 'object';
    // one NL variable forced to mean two different Lean terms
    if (/INCONSISTENT/.test(n.note)) {
      const m = n.note.match(/variable (\S+) maps to INCONSISTENT Lean terms \(([^)]+)\)/);
      const v = m ? m[1] : '?';
      const parts = m ? m[2].split(', ').map((x) => x.replace(/^v:|^c:|^app:c:|^app:|^lit:|^tuple:/, '')) : [];
      return `NL ${v} maps to {${parts.join(', ')}}. must be one thing.`;
    }
    // one ∀ vs two ∀ (note mentions "Lean binds another ∀", so test before Lean-only)
    if (/another ∀/.test(n.note)) return `NL binds 1 variable, Lean binds 2. does not match.`;
    // Lean has something NL does not (Lean-only piece / extra binder / extra operand)
    if (n.fol == null || /Lean binds|Lean defines|operand has no FOL|extra Lean/.test(n.note)) return `in Lean, not in NL.`;
    // NL has something Lean does not (maps to nothing / no counterpart)
    if (/maps to nothing|no Lean binder|no Lean counterpart|has no Lean counterpart|operand has no Lean|extra FOL/.test(n.note)) return `in NL, not in Lean.`;
    // body ∧-halt: Lean body is a single non-∧ shape
    const single = n.note.match(/single (\w+)/);
    if (single) return `Lean body is ${plainLean(single[1])}. NL body is ${plainKind(kind)}. does not match.`;
    // count mismatch: N conjuncts vs M
    const cnt = n.note.match(/has (\d+) parts, Lean ∧ has (\d+)/);
    if (cnt) return `NL has ${cnt[1]} parts, Lean has ${cnt[2]}. does not match.`;
    // generic shape mismatch: "… vs Lean X" / "… but Lean is X"
    const vs = n.note.match(/(?:vs|but) Lean (?:is )?(\w+)/);
    if (vs) return `Lean is ${plainLean(vs[1])}. NL is ${plainKind(kind)}. does not match.`;
    return n.note;
  }
  // plain one-word names (no symbols) for the simple body shape-mismatch message.
  function plainLean(t) {
    return ({ forall: 'forall', exists: 'exists', arrow: 'implication', and: 'and', or: 'or', not: 'not', eq: 'equality', mem: 'membership', app: 'application' })[t] || t;
  }
  function plainKind(k) {
    return ({ conjunction: 'and', disjunction: 'or', implication: 'implication', negation: 'not', universal: 'forall', existential: 'exists', equality: 'equality', relation: 'relation' })[k] || k;
  }
  // the .lean file path as stored in box.lean.spans (relative to pdf_direct_segment/,
  // i.e. "lean/MaxSupportKernel.lean") — matches how the Lean pane references files.
  function deriveLeanRel(assoc) {
    const base = assoc.src.split('/').pop();   // MaxSupportKernel.lean
    return 'lean/' + base;
  }
}
