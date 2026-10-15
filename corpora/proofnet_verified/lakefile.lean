import Lake
open Lake DSL

package ProofNetVerified

-- Domain-agnostic Pistis segmentation / faithfulness annotations (no Mathlib / no solver dep).
-- This is the LEAN-4.28 copy; `corpora/oai_math/Pistis/Segment.lean` is the 4.34 port. The two are
-- forked ONLY because Lean metaprogramming API cannot span toolchains — keep them diff-clean.
@[default_target]
lean_lib Pistis

-- This corpus's items, so backing files resolve as modules `items.item<N>.step<K>`.
lean_lib items

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

require Canonical from git
  "https://github.com/chasenorman/CanonicalLean.git" @ "v4.28.0"

require smt from git
  "https://github.com/ufmg-smite/lean-smt.git" @ "f58d19d5d0803fcccb5ccb1b4473774dd2ae9f9a"  -- The commit corresponds to v4.28.0
