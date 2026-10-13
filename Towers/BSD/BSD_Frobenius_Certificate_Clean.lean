/- BSD_Frobenius_Certificate_Clean.lean
   Visible copy of the algebraic Weil step from
   Towers/BSD/BSD_Frobenius_Certificate.lean.
   The source file has no imports and does not build.
   These two declarations are the existing proofs, not a new argument.
   BSD_FrobeniusDegreeNonneg_OPEN stays a Prop. No sorry. No new axiom.
-/

import Towers.BSD.BSD_LFunction
import Towers.BSD.BSD_FiberCount

namespace Towers.BSD

/-- Copied from BSD_Frobenius_Certificate.lean.
    Quadratic form r² − a_p r + p. Not the missing End(E) degree formula. -/
def BSD_FrobeniusDegreeNonneg_OPEN (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ r : ℝ, r ^ 2 - (a_p p : ℝ) * r + (p : ℝ) ≥ 0

/-- Copied from BSD_Frobenius_Certificate.lean. Algebra only. -/
theorem BSD_weil_discriminant_step (c : ℝ) (p : ℝ) (_hp : 0 < p)
    (h : ∀ r : ℝ, r ^ 2 - c * r + p ≥ 0) :
    |c| ≤ 2 * Real.sqrt p := by
  have hc2 : c ^ 2 ≤ 4 * p := by nlinarith [h (c / 2)]
  have hsqrt4p : (2 : ℝ) * Real.sqrt p = Real.sqrt (4 * p) := by
    rw [show (4 : ℝ) * p = (2 : ℝ) ^ 2 * p by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 2)]
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  rw [hsqrt4p, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hc2

/-- Copied from BSD_Frobenius_Certificate.lean.
    The original is not `private`, but that file does not build, so the
    Hasse point files could not see it. -/
theorem BSD_hasse_of_degree_nonneg (p : ℕ) [hp : Fact p.Prime]
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : BSD_Hasse_OPEN p :=
  BSD_weil_discriminant_step (a_p p : ℝ) (p : ℝ)
    (by exact_mod_cast hp.out.pos) h

end Towers.BSD
