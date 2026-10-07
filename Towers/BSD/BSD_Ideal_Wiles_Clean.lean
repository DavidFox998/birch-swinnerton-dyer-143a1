/-
  Partial Group G. The conductor factorization `143 = 11 * 13`.

  11 and 13 are prime, both divide 143, and both lie outside the checked
  set. That is `BSD_Ceiling_Theorem`. This file does not evaluate
  `E143_Finset` at either prime.

  The ideal equalities for 𝔭₂, 𝔭₃, and 𝔭₇, Wiles–Taylor, and `α_BSD_period`
  stay NEEDS_AUTHORING. The assessed names are `True`. `α_BSD_period` is
  not defined in this repository. Those equalities do not prove the
  ideal statements. No sorry.
-/

import Towers.BSD.BSD_More_Theorems_From_54

namespace Towers.BSD

/-- `143 = 11 * 13`. Both factors are prime, both divide 143, and both
    lie outside `BSD_Finite_Hasse_CheckedPrimes`. The ideal, Wiles–Taylor,
    and period names stay the placeholder `True`. -/
theorem BSD_conductor_factors :
    143 = 11 * 13 ∧
      Nat.Prime 11 ∧ Nat.Prime 13 ∧
      11 ∣ 143 ∧ 13 ∣ 143 ∧
      11 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      13 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      Towers_BSD_BSD_ClassNumber_UpperBound_CLOSED_Assessed.BSD_w3_ideal_equality_OPEN_prop = True ∧
      Towers_BSD_BSD_ClassNumber_UpperBound_CLOSED_Assessed.BSD_w4_ideal_equality_OPEN_prop = True ∧
      Towers_BSD_BSD_SurfaceClose_CLOSED_Assessed.BSD_w3_ideal_equality_CLOSED_prop = True ∧
      Towers_BSD_BSD_SurfaceClose_CLOSED_Assessed.BSD_w4_ideal_equality_CLOSED_prop = True ∧
      Towers_BSD_BSD_Ramanujan_from_Discriminant_Assessed.BSD_WilesTaylor_143_OPEN_prop = True ∧
      Towers_BSD_BSD_TranscendentalSieve_Assessed.BSD_Tier2B_ProvedFacts_prop = True ∧
      (84 : ℕ) ≠ 54 := by
  have hceil := BSD_Ceiling_Theorem
  refine ⟨by decide, by decide, by decide,
      hceil.2.2.2.2.2.1, hceil.2.2.2.2.2.2.1,
      hceil.2.2.2.1, hceil.2.2.2.2.1,
      rfl, rfl, rfl, rfl, rfl, rfl, BSD_54_of_504.2.2⟩

end Towers.BSD
