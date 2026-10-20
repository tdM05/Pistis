# Pistis

Oracle-guided search that formalizes a natural-language proof into a Lean proof satisfying five
necessary conditions of *faithfulness* — the formal proof mirrors how the NL argument reaches its
conclusion, step by step, under the same assumptions, in the same order.

The method is described in [`doc/pistis.pdf`](doc/pistis.pdf) (*Does the Proof Prove It That Way?
Faithful Formalization of Elements Proofs*), whose case study is Euclid's *Elements*, Books I–III.
This repository is the **domain-agnostic** generalization: `Pistis/Segment.lean` depends on no
particular theory and no solver, and each target corpus is a separate case study under `corpora/`.

## Layout

```
scripts/                  SHARED — stage drivers + faithfulness gates (pure Python, no Lean)
tests/                    SHARED — unit tests for those scripts
.claude/skills/           SHARED — the three stage skills: pistis-split, pistis-map, pistis-fill-naive
doc/pistis.pdf            the paper
corpora/
  proofnet_verified/      corpus 1 — ProofNet-Verified       (Lean 4.28.0)
  oai_math/               corpus 2 — openai/math preprints   (Lean 4.34.1)
```

Each corpus is an **independent Lake package**: its own `lakefile.lean`, `lean-toolchain`,
`lake-manifest.json`, and `.lake/`. They never resolve one another. Only `scripts/`, `tests/` and
`.claude/skills/` sit above both and are shared.

```
corpora/<corpus>/
  lakefile.lean  lean-toolchain  lake-manifest.json  .lake/
  Pistis.lean  Pistis/Segment.lean      the pistis_* tactics, for THIS toolchain
  items/item<N>/
    meta.json                           name, source, index (the locator prefix)
    data/nl_statement.txt               the NL statement — verbatim bytes, the intro's tiling target
    data/nl_proof.txt                   the NL proof — verbatim bytes, the text that must be tiled
    data/statement.lean                 the frozen formal statement (signature; body `sorry`)
    split.json                          stage 1 output: ordered atomic segments
    Main.lean                           stage 2 output: one Lean claim per segment
    step<K>.lean                         stage 3 output: one backing lemma per segment
```

### Why two packages

`corpora/proofnet_verified` is on Lean **4.28.0** with Mathlib `v4.28.0`.
`corpora/oai_math` is on Lean **4.34.1** with Mathlib pinned to `d13f23b7…` — the exact commit
[openai/math](https://github.com/openai/math) resolves, so a statement lifted out of their
`lean/OAI/...` tree means in our package exactly what it means in theirs. Six Lean releases apart is
not reconcilable inside one Lake package, so the toolchain-coupled layer is forked and everything
else is shared.

`oai_math` deliberately requires **Mathlib only** — not openai/math's other ~35 dependencies, nor the
patch-applying `run_cmd` in their lakefile. Add a `require` there only when a specific item cites a
result that lives outside Mathlib.

### `Pistis/Segment.lean` is forked per toolchain

There are two copies, one per Lean version, because Lean metaprogramming API cannot span toolchains.
They are currently **byte-identical** — the 4.28 source compiles unchanged on 4.34.1 — so keep them
diff-clean and expect nothing but genuine port deltas:

```sh
diff corpora/proofnet_verified/Pistis/Segment.lean corpora/oai_math/Pistis/Segment.lean
```

## Running a stage

Stage commands run with **cwd = the corpus package root**, and an item is addressed as
`items/item<N>`. That keeps `lake` and the scripts agreeing on one path:

```sh
cd corpora/proofnet_verified
python3 ../../scripts/check_split.py items/item1     # tiling gate
lake env lean items/item1/Main.lean                  # elaboration gate
```

First build of a corpus needs its Mathlib oleans, which are not in git:

```sh
cd corpora/<corpus> && lake exe cache get && lake build Pistis
```

Measured cost of the inner loop (single file, `import Mathlib`, warm page cache, network home dir):
**~52s** on `oai_math` / 4.34.1, **~60s** on `proofnet_verified` / 4.28.0. Cold it is ~3min. The map
and fill stages build after every segment, so budget accordingly.

## Stages

1. **`/pistis-split`** — text only. Partition `nl_proof` into atomic segments, each with an
   `assumptions` set and a single `assert`. Gated on byte-exact tiling of the source.
2. **`/pistis-map`** — translation, not proving. One Lean claim type per segment; every body stays
   `:= by sorry`. Gated on tiling, no vacuous claim, no stray `sorry`, unchanged signature.
3. **`/pistis-fill-naive`** — proving. Each segment gets its own `step<K>.lean` backing lemma; `Main`
   delegates and supplies every hypothesis through `pistis_assumption`. Gated on zero `sorry`.

The ground-truth / baseline proof is never read at any stage — that is contamination, and it defeats
the point of measuring whether the NL argument itself formalizes.

## Known gaps

- Three scripts the skills invoke do not exist yet: `check_signatures.py` (map + fill gates),
  `check_steps.py --save` (freezes human-approved claims), `check_backing.py` (fill-stage structure
  gate). The map stage's hard gate cannot pass as written until these land. They are shared code.
- The skills still document the pre-restructure invocation (`proofnet_verified/item8`, scripts at
  `scripts/...`); they need updating to the cwd + `items/item<N>` convention above.
- `corpora/oai_math/items/item1` has its inputs (`meta.json`, `data/nl_statement.txt`,
  `data/nl_proof.txt`, `data/statement.lean`,
  `data/source.tex`) but no `split.json` / `Main.lean` / `step<K>.lean` yet — the three stages have
  not been run on it.

## The NL source format

Each item stores its two NL texts as **plain UTF-8 files whose bytes are the text**:
`data/nl_statement.txt` and `data/nl_proof.txt`. No JSON escaping, no trailing newline, nothing
normalized. Every gate here compares these texts byte-for-byte, so the storage format is the bytes
themselves — which is also what makes them searchable: you can `grep -F -f data/nl_proof.txt
<paper>.tex`, or Ctrl-F a line of the file in the paper, and get a hit. (These were previously one
`nl.json` per item with `nl_statement`/`nl_proof` string fields. JSON must escape a newline as the
two characters `\` `n` and double every LaTeX backslash, so the bytes on disk were not the bytes of
the text and searching for what you saw in the file found nothing. `scripts/convert_nl_to_txt.py`
performed the migration and can re-verify it against git history.)

### Everything else is derived from those two files

The `.txt` files are the source. Every other representation of the NL is **derived**, and the point
of listing the generator next to each one is that you never have to take anyone's word for an
artifact: re-run the script and diff. Each of these is idempotent — a re-run reproduces the existing
bytes exactly, so a diff is the whole audit.

| artifact | generator | input |
| --- | --- | --- |
| `data/nl_{statement,proof}.txt` (oai_math) | `scripts/extract_tex.py` | the paper's `.tex` + the anchors in `meta.json` → `nl_source.slice` |
| `data/nl_{statement,proof}.txt` (proofnet) | `corpora/proofnet_verified/items/_source/extract_nl.py` | `_source/proofnet-verified.jsonl` |
| `split.json` | **authored** (the `pistis-split` skill) | gated by `scripts/check_split.py` to tile the `.txt` byte-for-byte |
| `Main.lean` NL literals | `scripts/scaffold_main.py` | `split.json` (claims are then filled by the map stage) |
| `align/*/artifacts/` | `faithfulness/gen_datapoints.py`, then `faithfulness/annotate_item1.py` | `Main.lean` + the `.txt` |
| `kpistis/units/` | `kpistis/build.py`, then `kpistis/annotate_item1.py` | `Proof.lean` + the `.txt` |

Only `split.json` is authored rather than computed — where one segment ends and the next begins is a
judgment. It is not trusted either: `check_split.py` holds its segments to tiling the `.txt` exactly,
and `check_main.py` holds `Main.lean` to the same bytes independently.

A derived format may have to escape (JSON must, and `split.json` does). That is fine where the format
demands it, but **not** where the format offers a verbatim option. Lean has raw literals (`r"…"`, or
`r#"…"#` when the text contains a quote), Python has raw strings, Markdown has code fences — so NL in
`Main.lean`, in the `annotate_item1.py` generators and in a ` ```lean ` fence is stored verbatim, and
the file's bytes are the paper's bytes. JSON has no verbatim option and is the one exemption.

Two gates hold this, because checks on string *values* cannot see the difference — an escaped
`"…\\subseteq…"` decodes correctly, so coverage reported "reproduces source exactly" while the file
said something the paper never did and Ctrl-F found nothing:

```sh
python3 ../../scripts/check_main.py items/item1   # check 5: each segment's NL text, verbatim in Main.lean
python3 scripts/check_nl_verbatim.py              # repo-wide: no file holds an NL line escaped
```

The second is Ctrl-F with nothing in between: for every line of every `data/nl_*.txt`, no file may
contain that line with its backslashes doubled unless it also contains the line itself. A value check
and a byte check are different checks; this repo needs both, and only had the first.

## Extracting the NL text from LaTeX

ProofNet ships its NL text ready-made; openai/math ships prose as `.tex`, so the statement and proof
must be located in the paper. `scripts/extract_tex.py` cuts them as **verbatim contiguous
substrings** — literal `src[a:b]` at offsets found by unique anchor strings:

```sh
cd corpora/oai_math
python3 ../../scripts/extract_tex.py --tex <paper>/02-pruning.tex --out items/item1/data \
    --stmt-from 'For finite index sets' --stmt-to 'one has $x_jy_s=0$.' \
    --proof-from 'Suppose instead that' --proof-to 'a contradiction.'
```

Nothing is unwrapped, reflowed or macro-expanded: the author's hard line wraps stay where they are
mid-sentence, two spaces after a period stay two spaces, `\[ ... \]` keeps its newlines and indent,
and `\R`/`\im`/`\rank` stay unexpanded (`meta.json` records what they mean). Whitespace and LaTeX
*are* the text — the split stage is gated on tiling these bytes exactly, so tidying them here would
silently rewrite the source of truth. Each item's anchors are stored in `meta.json` → `nl_source.slice`.

`--stmt-from` is deliberately set **before** `\begin{lemma}`, far enough back to include the sentence
that defines the term the statement then uses ("a matrix supported on $T$"), and no further — the two
sentences above it describe *Lemma 3.1's* proof strategy and assert nothing about this lemma.
