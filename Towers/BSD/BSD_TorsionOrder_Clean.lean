/-
  Partial Group F, continued. `(2, 0)` is not a 2-torsion point.

  On `y² + y = x³ - x² - x - 2`, Mathlib's affine group law gives a point
  `P = (2, 0)`. Its negative is `(2, -1)`. These are distinct, so `P + P ≠ 0`,
  hence `2 • P ≠ 0`.

  This does not prove that the order is infinite. It does not prove that `P`
  generates `E(ℚ)`, that the Mordell–Weil rank is 1, or BSD.
  `BSD_TorsCard` is the constant 1 in the registry, not a count of `E(ℚ)`.
  The 54 assessed definitions in this group were not rewritten.
  No new `E143_Finset` enumeration. No sorry.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Towers.BSD.BSD_Torsion_Rank_Clean

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace Towers.BSD

def E143Q : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -1, a₆ := -2 }

theorem E143Q_nonsingular_two_zero : Nonsingular E143Q (2 : ℚ) 0 := by
  rw [nonsingular_iff, equation_iff]
  dsimp [E143Q]
  constructor
  · norm_num
  · right
    norm_num

theorem E143Q_negY_two_zero : negY E143Q 2 0 = -1 := by
  dsimp [negY, E143Q]
  norm_num

def E143Q_P20 : Point E143Q :=
  Point.some E143Q_nonsingular_two_zero

private def yCoord (P : Point E143Q) : Option ℚ :=
  Point.casesOn P none (fun {_x y} _ => some y)

theorem E143Q_P20_ne_neg : E143Q_P20 ≠ -E143Q_P20 := by
  intro h
  have hy : yCoord E143Q_P20 = yCoord (-E143Q_P20) := congrArg yCoord h
  rw [E143Q_P20, neg_some] at hy
  dsimp [yCoord] at hy
  rw [E143Q_negY_two_zero] at hy
  injection hy

/-- `2 • (2, 0) ≠ 0` in the Mathlib affine group. Not infinite order,
    not a generator, not rank 1, not BSD. -/
theorem BSD_affine_not_two_torsion : (2 : ℕ) • E143Q_P20 ≠ 0 := by
  intro h
  have hsum : E143Q_P20 + E143Q_P20 = 0 := by
    rw [show (2 : ℕ) • E143Q_P20 = E143Q_P20 + E143Q_P20 by
      rw [show (2 : ℕ) = 1 + 1 from rfl, add_nsmul, one_nsmul]] at h
    exact h
  exact E143Q_P20_ne_neg ((eq_neg_iff_add_eq_zero).2 hsum)

/-- The checked affine membership still holds. The new group-law fact is
    `2 • P ≠ 0`. The registry torsion, Tamagawa, regulator, Néron–Tate,
    Heegner, Gross–Zagier, Kolyvagin, and Sha names stay placeholders. -/
theorem BSD_affine_still_not_rank
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    ((2 : ZMod p), (0 : ZMod p)) ∈ E143_Finset p ∧
      (2 : ℕ) • E143Q_P20 ≠ 0 ∧
      BSD_MissingDefinitionsRegistry.BSD_TorsCard = 1 ∧
      BSD_MissingDefinitionsRegistry.BSD_TamagawaProd = 1 ∧
      (84 : ℕ) ≠ 54 :=
  ⟨BSD_affine_point_in_E143_Finset_checked p hp, BSD_affine_not_two_torsion,
    rfl, rfl, BSD_54_of_504.2.2⟩

end Towers.BSD
