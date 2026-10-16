import Lake
open Lake DSL

package OAIMath where
  -- Pin the toolchain: this corpus must elaborate against the SAME Lean as openai/math, so that a
  -- formal statement lifted out of their `lean/OAI/...` tree means exactly what it means there.
  fixedToolchain := true
  -- Mirrors openai/math's `lean/lakefile.lean`. With autoImplicit ON, a typo in a lifted statement
  -- silently becomes a new implicit universe/type variable instead of erroring — which would let a
  -- subtly-wrong statement pass the map stage. Keep it OFF, exactly as upstream has it.
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Domain-agnostic Pistis segmentation / faithfulness annotations (no Mathlib / no solver dep).
-- This is the LEAN-4.34 copy; `corpora/proofnet_verified/Pistis/Segment.lean` is the 4.28 original.
-- The two are forked ONLY because Lean metaprogramming API cannot span toolchains — keep them
-- diff-clean: `diff corpora/*/Pistis/Segment.lean` should show nothing but genuine port deltas.
@[default_target]
lean_lib Pistis

-- This corpus's items, so backing files resolve as modules `items.item<N>.step<K>`.
lean_lib items

-- Mathlib ONLY, pinned to the exact commit openai/math resolves (see their lake-manifest.json), so
-- every Mathlib name and notation is identical to the environment their formalizations were written
-- in. Deliberately NOT mirroring their other ~35 dependencies or the patch-applying `run_cmd` in
-- their lakefile: no item needs them yet, and they bring long builds plus patch breakage. Add a
-- `require` here only when a specific item actually cites a result that lives outside Mathlib.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
