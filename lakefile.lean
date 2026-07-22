import Lake
open Lake DSL

package birch_swinnerton_dyer_143a1 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

@[default_target]
lean_lib «lean» where
  srcDir := "lean"

lean_lib HassePrimeSet where

lean_lib BostBound143 where

lean_lib hasseprimset where
  srcDir := "hasseprimset"
