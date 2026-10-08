/-
  Group E, rewritten under a new name.

  `Re(s) > 3/2` implies `Re(2 - s) < 1/2`. The half-plane of absolute
  convergence is not symmetric under `s ↦ 2 - s`. Analytic continuation
  and the functional equation are not in Mathlib v4.12.0.
  The 11 assessed definitions were not rewritten. No sorry.
-/

import Towers.BSD.BSD_AnalyticContinuation_Clean

namespace Towers.BSD

theorem BSD_halfplane_asymmetry (s : ℂ) (hs : (3 : ℝ) / 2 < s.re) :
    ((2 : ℂ) - s).re < (1 : ℝ) / 2 :=
  BSD_absconv_halfplane_not_symmetric s hs

theorem BSD_continuation_new_still_open :
    BSD_MissingDefinitionsRegistry.BSD_EulerConvergence_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_FuncEq_OPEN = True ∧
      (∀ s : ℂ, (3 : ℝ) / 2 < s.re → ((2 : ℂ) - s).re < (1 : ℝ) / 2) ∧
      (84 : ℕ) ≠ 54 :=
  ⟨rfl, rfl, BSD_halfplane_asymmetry, BSD_54_of_504.2.2⟩

end Towers.BSD
