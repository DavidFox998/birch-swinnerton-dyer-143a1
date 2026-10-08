/-
  Group F, rewritten under the clean names.

  `BSD_reduction_hom_secant` is the chord case already compiled: when the
  integer `x`-coordinates stay distinct modulo `p`, the reduced slope,
  `addX`, and `negAddY` match the formulas over `ZMod p`.
  `BSD_negY_on_reduction` is `negY = -y - 1`.

  The tangent case is not a theorem. Mathlib v4.12.0 has no elliptic formal
  group, and `Int.castRingHom (ZMod p)` is not injective, so `map_slope`
  does not define `E(ℚ) → E(𝔽_p)`.

  `BSD_torsion_trivial` is Lagrange for injective homs of the torsion
  subgroup into `Point (E143Fp 3)` and `Point (E143Fp 5)`, whose orders are
  the proved values `5` and `7`. The homs are hypotheses.
  `BSD_rank_ge_one_unconditional` is not a theorem. The embedding of `ℤ`
  stays conditional on those homs, under the name already compiled,
  `BSD_rank_ge_one_of_reduction`.

  Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, the regulator,
  Néron–Tate height, and the BSD formula stay NEEDS_AUTHORING.
  The 54 assessed definitions were not rewritten. No sorry.
-/

import Towers.BSD.BSD_ReductionHom_Clean

open WeierstrassCurve WeierstrassCurve.Affine

namespace Towers.BSD

/-- Secant slope for integral points whose `x`-coordinates stay distinct modulo `p`. -/
theorem BSD_reduction_hom_secant
    (p : ℕ) [Fact p.Prime] (x₁ x₂ y₁ y₂ : ℤ)
    (hx : ((x₁ : ℤ) : ZMod p) ≠ x₂) :=
  BSD_secant_slope_reduces p x₁ x₂ y₁ y₂ hx

/-- The chord formula for the third intersection, under the same hypothesis. -/
theorem BSD_reduction_hom_secant_addX
    (p : ℕ) [Fact p.Prime] (x₁ x₂ y₁ y₂ : ℤ)
    (hx : ((x₁ : ℤ) : ZMod p) ≠ x₂) :=
  BSD_addX_secant_reduces p x₁ x₂ y₁ y₂ hx

/-- `negAddY` on that chord. -/
theorem BSD_reduction_hom_secant_negAddY
    (p : ℕ) [Fact p.Prime] (x₁ x₂ y₁ y₂ : ℤ)
    (hx : ((x₁ : ℤ) : ZMod p) ≠ x₂) :=
  BSD_negAddY_secant_reduces p x₁ x₂ y₁ y₂ hx

/-- Negation on the reduced curve is the polynomial `-y - 1`. -/
theorem BSD_negY_on_reduction (p : ℕ) [Fact p.Prime] (x y : ℤ) :
    negY (E143Fp p) (x : ZMod p) (y : ZMod p) = ((-y - 1 : ℤ) : ZMod p) :=
  BSD_negY_reduces p x y

/-- Torsion is trivial if it injects into the two groups of orders `5` and `7`.
    The injections are hypotheses. They are not constructed from a formal group. -/
theorem BSD_torsion_trivial
    (f : ↥(AddCommGroup.torsion (Point E143Q)) →+ Point (E143Fp 3))
    (hf : Function.Injective f)
    (g : ↥(AddCommGroup.torsion (Point E143Q)) →+ Point (E143Fp 5))
    (hg : Function.Injective g)
    {a : Point E143Q} (ha : IsOfFinAddOrder a) : a = 0 :=
  BSD_torsion_trivial_of_coprime_cards BSD_point_card_p3 BSD_point_card_p5
    (by decide) f hf g hg ha

/-- The secant case, the orders `5` and `7`, and the failure of injectivity
    of `ℤ → ZMod p`. The tangent case and unconditional rank are not here.
    `84 ≠ 54`. -/
theorem BSD_torsion_rank_still_conditional :
    ¬ Function.Injective (Int.castRingHom (ZMod 3)) ∧
      ¬ Function.Injective (Int.castRingHom (ZMod 5)) ∧
      Nat.card (Point (E143Fp 3)) = 5 ∧
      Nat.card (Point (E143Fp 5)) = 7 ∧
      negY (E143Fp 3) (2 : ZMod 3) 0 = -1 ∧
      (2 : ℕ) • E143Q_P20 ≠ 0 ∧
      (84 : ℕ) ≠ 54 :=
  ⟨BSD_intCast_not_injective 3, BSD_intCast_not_injective 5,
    BSD_point_card_p3, BSD_point_card_p5,
    BSD_neg_two_zero_reduces 3, BSD_affine_not_two_torsion, BSD_54_of_504.2.2⟩

end Towers.BSD
