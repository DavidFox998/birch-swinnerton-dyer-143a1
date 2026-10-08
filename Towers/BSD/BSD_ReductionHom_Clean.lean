/-
  Partial Group F, continued. The chord case of reduction.

  Mathlib's `map_slope` identifies the slope over `F` with the slope over `K`
  for a ring homomorphism `F →+* K` of fields, and the proof uses injectivity
  of that homomorphism. `Int.castRingHom (ZMod p)` sends `p` and `0` to `0`,
  so it is not injective. That lemma does not define `E(ℚ) → E(𝔽_p)`.

  What does compile is the secant case for integral coordinates. If `x₁` and
  `x₂` remain distinct modulo `p`, the slope `(y₁ - y₂) / (x₁ - x₂)` is a
  `p`-integral rational, and its reduction equals the slope over `ZMod p`.
  `addX` and `negAddY` are polynomials in that slope, so they reduce as well.
  Negation is polynomial and reduces for every integral point.

  The tangent case, a point whose denominator is divisible by `p`, and the
  proof that prime-to-`p` torsion lies outside that kernel, are the formal
  group. Mathlib v4.12.0 has no elliptic formal group. Unconditional trivial
  torsion and rank at least 1 stay NEEDS_AUTHORING. Gross–Zagier, Kolyvagin,
  Heegner, Sha, Tamagawa, the regulator, Néron–Tate height, and the BSD formula
  stay NEEDS_AUTHORING. The 54 assessed definitions were not rewritten.
  No new `E143_Finset` enumeration. No sorry.
-/

import Mathlib.Data.Rat.Lemmas
import Towers.BSD.BSD_Reduction_Clean

open WeierstrassCurve WeierstrassCurve.Affine

namespace Towers.BSD

theorem BSD_intCast_not_injective (p : ℕ) [Fact p.Prime] :
    ¬ Function.Injective (Int.castRingHom (ZMod p)) := by
  intro hinj
  have h0 : (Int.castRingHom (ZMod p)) (p : ℤ) = (Int.castRingHom (ZMod p)) 0 := by
    simp only [Int.coe_castRingHom, Int.cast_zero, Int.cast_natCast]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd p p).mpr (dvd_refl p)
  have hp0 : (p : ℤ) = 0 := hinj h0
  have : p = 0 := by exact_mod_cast hp0
  exact (Fact.out : Nat.Prime p).ne_zero this

/-- Reducing a ratio of integers whose denominator is nonzero modulo `p`. -/
theorem BSD_rat_div_reduces (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (hb : ((b : ℤ) : ZMod p) ≠ 0) :
    (((a : ℚ) / (b : ℚ)).num : ZMod p) * (((a : ℚ) / (b : ℚ)).den : ZMod p)⁻¹
      = (a : ZMod p) * (b : ZMod p)⁻¹ := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (by simp)
  have hq : (a : ℚ) / (b : ℚ) = Rat.divInt a b := (Rat.divInt_eq_div a b).symm
  obtain ⟨c, ha, hd⟩ := Rat.num_den_mk hb0 hq
  have hden : (((a : ℚ) / (b : ℚ)).den : ZMod p) ≠ 0 := by
    intro h0
    apply hb
    have hd' : (b : ZMod p) = (c : ZMod p) * (((a : ℚ) / (b : ℚ)).den : ZMod p) := by
      have hcast := congrArg (fun t : ℤ => (t : ZMod p)) hd
      simpa [Int.cast_mul, Int.cast_natCast] using hcast
    rw [hd', h0, mul_zero]
  have hcross : (((a : ℚ) / (b : ℚ)).num : ℤ) * b
      = a * (((a : ℚ) / (b : ℚ)).den : ℤ) := by
    rw [ha, hd]
    ring
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hden hb]
  exact_mod_cast hcross

theorem BSD_negY_reduces (p : ℕ) [Fact p.Prime] (x y : ℤ) :
    negY (E143Fp p) (x : ZMod p) (y : ZMod p) = (negY E143Z x y : ZMod p) := by
  have hZ : negY E143Z x y = -y - 1 := by
    simp [negY, E143Z]
  rw [hZ]
  simp only [negY, E143Fp, E143Z, map_a₁, map_a₃, map_zero, map_one,
    Int.cast_neg, Int.cast_sub, Int.cast_one]
  ring

/-- Secant slope. The hypothesis is that the `x`-coordinates stay distinct
    modulo `p`, so the case split does not change under reduction. -/
theorem BSD_secant_slope_reduces (p : ℕ) [Fact p.Prime] (x₁ x₂ y₁ y₂ : ℤ)
    (hx : ((x₁ : ℤ) : ZMod p) ≠ x₂) :
    let s : ℚ := ((y₁ - y₂ : ℤ) : ℚ) / ((x₁ - x₂ : ℤ) : ℚ)
    ((s.num : ZMod p) * (s.den : ZMod p)⁻¹)
      = slope (E143Fp p) (x₁ : ZMod p) x₂ (y₁ : ZMod p) y₂ := by
  intro s
  have hΔ : ((x₁ - x₂ : ℤ) : ZMod p) ≠ 0 := by
    simpa [Int.cast_sub, sub_ne_zero] using hx
  have hs := BSD_rat_div_reduces p (y₁ - y₂) (x₁ - x₂) hΔ
  rw [hs, slope_of_X_ne hx]
  simp [Int.cast_sub, div_eq_mul_inv]

theorem BSD_addX_secant_reduces (p : ℕ) [Fact p.Prime] (x₁ x₂ y₁ y₂ : ℤ)
    (hx : ((x₁ : ℤ) : ZMod p) ≠ x₂) :
    let s : ℚ := ((y₁ - y₂ : ℤ) : ℚ) / ((x₁ - x₂ : ℤ) : ℚ)
    let L : ZMod p := (s.num : ZMod p) * (s.den : ZMod p)⁻¹
    L ^ 2 + 1 - (x₁ : ZMod p) - x₂
      = addX (E143Fp p) (x₁ : ZMod p) x₂
          (slope (E143Fp p) (x₁ : ZMod p) x₂ (y₁ : ZMod p) y₂) := by
  intro s L
  have hs : L = slope (E143Fp p) (x₁ : ZMod p) x₂ (y₁ : ZMod p) y₂ :=
    BSD_secant_slope_reduces p x₁ x₂ y₁ y₂ hx
  rw [hs]
  simp only [addX, E143Fp, E143Z, map_a₁, map_a₂, map_zero, map_neg, map_one]
  ring

theorem BSD_negAddY_secant_reduces (p : ℕ) [Fact p.Prime] (x₁ x₂ y₁ y₂ : ℤ)
    (hx : ((x₁ : ℤ) : ZMod p) ≠ x₂) :
    let s : ℚ := ((y₁ - y₂ : ℤ) : ℚ) / ((x₁ - x₂ : ℤ) : ℚ)
    let L : ZMod p := (s.num : ZMod p) * (s.den : ZMod p)⁻¹
    let X : ZMod p := L ^ 2 + 1 - x₁ - x₂
    L * (X - x₁) + y₁
      = negAddY (E143Fp p) (x₁ : ZMod p) x₂ (y₁ : ZMod p)
          (slope (E143Fp p) (x₁ : ZMod p) x₂ (y₁ : ZMod p) y₂) := by
  intro s L X
  have hX : X = addX (E143Fp p) (x₁ : ZMod p) x₂
      (slope (E143Fp p) (x₁ : ZMod p) x₂ (y₁ : ZMod p) y₂) :=
    BSD_addX_secant_reduces p x₁ x₂ y₁ y₂ hx
  have hs : L = slope (E143Fp p) (x₁ : ZMod p) x₂ (y₁ : ZMod p) y₂ :=
    BSD_secant_slope_reduces p x₁ x₂ y₁ y₂ hx
  rw [hX, hs]
  simp only [negAddY]

/-- `(2, 0)` and its negative `(2, -1)` reduce to negatives of one another. -/
theorem BSD_neg_two_zero_reduces (p : ℕ) [Fact p.Prime] :
    negY (E143Fp p) (2 : ZMod p) 0 = (-1 : ZMod p) := by
  have h := BSD_negY_reduces p 2 0
  have hZ : negY E143Z 2 0 = -1 := by
    simp [negY, E143Z]
  simpa [hZ] using h

/-- The secant identities and the failure of injectivity. They do not give a
    homomorphism `E(ℚ) → E(𝔽_p)`, trivial torsion, or rank at least 1.
    `84 ≠ 54`. -/
theorem BSD_reductionHom_still_open :
    ¬ Function.Injective (Int.castRingHom (ZMod 3)) ∧
      ¬ Function.Injective (Int.castRingHom (ZMod 5)) ∧
      Nat.card (Point (E143Fp 3)) = 5 ∧
      Nat.card (Point (E143Fp 5)) = 7 ∧
      negY (E143Fp 3) (2 : ZMod 3) 0 = -1 ∧
      negY (E143Fp 5) (2 : ZMod 5) 0 = -1 ∧
      (84 : ℕ) ≠ 54 := by
  exact ⟨BSD_intCast_not_injective 3, BSD_intCast_not_injective 5,
    BSD_point_card_p3, BSD_point_card_p5,
    BSD_neg_two_zero_reduces 3, BSD_neg_two_zero_reduces 5,
    BSD_54_of_504.2.2⟩

end Towers.BSD
