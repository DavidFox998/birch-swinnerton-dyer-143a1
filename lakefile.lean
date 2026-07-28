import Lake
open Lake DSL

package birch_swinnerton_dyer_143a1

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

-- Main 8 files in lean/ — 01,02,03_closed, BQF, S4, C5,C6,C7 + Honest HasseWiles
@[default_target]
lean_lib «lean» where
  srcDir := "lean"

-- Root aggregates
lean_lib HassePrimeSet where
  srcDir := "."

lean_lib BostBound143 where
  srcDir := "."

-- Tier C 127 files — hasseprimset/BSD_Genesis*.lean
lean_lib hasseprimset where
  srcDir := "."

-- Towers/BSD/ — Genesis 762, 763 honest point counts
lean_lib Towers where
  srcDir := "."
