import Lake
open Lake DSL

package birch_swinnerton_dyer_143a1 where
  -- keep package name exactly as repo

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

-- Main 8 files in lean/ — honest path
-- 01_genus_X0_143, 02_hecke_operators, 03_qexpansion_closed_HONEST, BQF, S4, C5,C6,C7 + HasseWiles HONEST
@[default_target]
lean_lib lean where
  srcDir := "lean"

-- Root aggregates — BSD_Hasse_1061_Primes_Audit_143a1.lean capstone
lean_lib BSD_Hasse_1061_Primes_Audit_143a1 where
  srcDir := "."

-- Bost bound S₄ = {2,3,19,191} C=11.422 >2√13
lean_lib BostBound143 where
  srcDir := "."

-- Tier C 127 files — hasseprimset/BSD_Genesis*.lean — 1061 primes 1009..9999
lean_lib hasseprimset where
  srcDir := "."

-- Towers/BSD/ — Genesis 762, 763 honest point counts via E143_Finset by decide
lean_lib Towers where
  srcDir := "."

-- Clean aggregation — only files that actually compile (13/243)
-- See BSD_Clean_Aggregation.lean for the honest baseline.
lean_lib BSD_Clean_Aggregation where
  srcDir := "."
