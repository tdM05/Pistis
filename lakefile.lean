import Lake
open Lake DSL

package Pistis

-- Domain-agnostic Pistis segmentation / faithfulness annotations (no Mathlib / no solver dep).
-- Shared by every case study; each corpus (proofnet-verified, textbooks, and eventually a
-- 4.28-ported LeanEuclidF) is added as its own lean_lib below.
@[default_target]
lean_lib Pistis

-- The ProofNet-Verified case study, so item backing files (item<N>.step<K>) resolve as modules.
lean_lib proofnet_verified

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

require Canonical from git
  "https://github.com/chasenorman/CanonicalLean.git" @ "v4.28.0"

require smt from git
  "https://github.com/ufmg-smite/lean-smt.git" @ "f58d19d5d0803fcccb5ccb1b4473774dd2ae9f9a"  -- The commit corresponds to v4.28.0
