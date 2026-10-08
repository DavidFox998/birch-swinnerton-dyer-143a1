/-
  Group C, rewritten under a new name.

  The compiled piece is one local factor: `BSD_goodLocalFactor 2 1 = 2/3`,
  and the product of the good factors over the 84 checked primes.
  `BSD_Rank 143 = 1` is the definition `if N = 143 then 1 else 0`.
  The registry derivative stays `0`. Modularity is not in Mathlib v4.12.0.
  The 12 assessed definitions were not rewritten. No sorry.
-/

import Towers.BSD.BSD_LFunction_HasseWeil_Clean

namespace Towers.BSD

theorem BSD_localFactor_at_two :
    BSD_goodLocalFactor 2 1 = (2 : ℂ) / 3 :=
  BSD_localFactor_two_at_one

theorem BSD_partial_euler_support :
    BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      11 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      13 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      11 ∣ 143 ∧ 13 ∣ 143 :=
  BSD_HasseWeil_partial_support

/-- The partial product is not the Hasse–Weil derivative. `L_143a1` stays `True`. -/
theorem BSD_hasseWeil_new_not_derivative :
    BSD_MissingDefinitionsRegistry.BSD_L143a1_DerivAtOne = (0 : ℝ) ∧
      BSD_MissingDefinitionsRegistry.L_143a1 = True ∧
      BSD_goodLocalFactor 2 1 = (2 : ℂ) / 3 ∧
      BSD_Rank 143 = 1 ∧
      (84 : ℕ) ≠ 54 :=
  ⟨rfl, rfl, BSD_localFactor_at_two, BSD_rank_placeholder_values.1, BSD_54_of_504.2.2⟩

end Towers.BSD
