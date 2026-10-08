/-
  Partial Group E, continued. The absolute-convergence half-plane is not
  symmetric under `s ↦ 2 - s`.

  If `Re(s) > 3/2`, then `Re(2 - s) < 1/2`. The Dirichlet series on
  `Re(s) > 3/2` does not, by itself, give values on the reflected half-plane.
  Analytic continuation and the functional equation need a modular form and
  the Fricke involution. Neither is in Mathlib v4.12.0.
  `EllipticLFunction` in `B01_EllipticCurve` is opaque and is not used.

  The checked-support bound from Group D, and the finite product from Group C,
  stay short of `BSD_EulerProduct_OPEN` and `BSD_LSeriesSummable_OPEN`.
  The 11 assessed definitions were not rewritten. No new point count. No sorry.
-/

import Mathlib.Data.Complex.Basic
import Towers.BSD.BSD_LFunction_HasseWeil_Clean
import Towers.BSD.BSD_PrimePower_Clean

namespace Towers.BSD

/-- Absolute convergence for `Re(s) > 3/2` does not give the reflected point.
    `Re(2 - s) = 2 - Re(s) < 1/2`. -/
theorem BSD_absconv_halfplane_not_symmetric (s : ℂ) (hs : (3 : ℝ) / 2 < s.re) :
    ((2 : ℂ) - s).re < (1 : ℝ) / 2 := by
  have hre : ((2 : ℂ) - s).re = 2 - s.re := by
    rw [Complex.sub_re]
    norm_num
  linarith

/-- The checked-support coefficient bound and the 84-factor product do not
    prove the Euler product, the functional equation, or summability over
    every positive integer. The registry names stay `True`. -/
theorem BSD_continuation_still_open :
    BSD_MissingDefinitionsRegistry.BSD_EulerConvergence_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_FuncEq_OPEN = True ∧
      BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      (84 : ℕ) ≠ 54 ∧
      (∀ s : ℂ, (3 : ℝ) / 2 < s.re → ((2 : ℂ) - s).re < (1 : ℝ) / 2) :=
  ⟨rfl, rfl, BSD_Finite_Hasse_CheckedPrimes_card, BSD_54_of_504.2.2,
    BSD_absconv_halfplane_not_symmetric⟩

end Towers.BSD
