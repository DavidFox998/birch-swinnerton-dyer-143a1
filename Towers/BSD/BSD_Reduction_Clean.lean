/-
  Partial Group F, continued. The Mathlib point group over `𝔽_p`.

  For a prime `p` that does not divide the curve discriminant `1859`, every
  affine solution of `y² + y = x³ - x² - x - 2` over `ZMod p` is nonsingular,
  by `WeierstrassCurve.Affine.nonsingular_of_Δ_ne_zero`. The Mathlib group
  `Point` is that set together with the point at infinity, so its cardinality
  is `(E143_Finset p).card + 1`. At the already compiled primes `3` and `5`
  this cardinality is `5` and `7`.

  An integral point reduces by `Int.castRingHom`. The point `(2, 0)` reduces
  to a non-identity point of `Point` over `ZMod p`.

  This file does not construct a homomorphism `E(ℚ) → E(𝔽_p)`. Mathlib v4.12.0
  has no reduction map on rational points and no proof that reduction is
  injective on the torsion subgroup. `BSD_rank_ge_one_of_reduction` therefore
  takes those two injective homomorphisms as hypotheses. Unconditional infinite
  order and rank exactly 1 stay NEEDS_AUTHORING. Gross–Zagier, Kolyvagin,
  Heegner, Sha, Tamagawa, the regulator, Néron–Tate height, and the BSD formula
  stay NEEDS_AUTHORING. The 54 assessed definitions were not rewritten.
  No new `E143_Finset` enumeration. No sorry.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Torsion
import Towers.BSD.BSD_RankAtLeastOne_Clean

open WeierstrassCurve WeierstrassCurve.Affine

namespace Towers.BSD

def E143Z : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -1, a₆ := -2 }

theorem E143Z_Δ : E143Z.Δ = -1859 := by
  simp only [E143Z, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

def E143Fp (p : ℕ) [Fact p.Prime] : WeierstrassCurve (ZMod p) :=
  E143Z.map (Int.castRingHom (ZMod p))

theorem E143Fp_Δ (p : ℕ) [Fact p.Prime] : (E143Fp p).Δ = (-1859 : ZMod p) := by
  rw [E143Fp, map_Δ, E143Z_Δ]
  simp [Int.coe_castRingHom]

theorem E143Fp_Δ_ne_zero_of_not_dvd (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 1859) :
    (E143Fp p).Δ ≠ 0 := by
  rw [E143Fp_Δ]
  intro h
  apply hp
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  exact neg_eq_zero.mp h

theorem E143Fp_equation_iff (p : ℕ) [Fact p.Prime] (x y : ZMod p) :
    Equation (E143Fp p) x y ↔ E143_point p x y := by
  rw [equation_iff, E143_point]
  simp only [E143Fp, E143Z, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_zero, map_one,
    map_neg, map_ofNat]
  constructor
  · intro h
    convert h using 1 <;> ring
  · intro h
    convert h using 1 <;> ring

theorem E143Fp_nonsingular_iff (p : ℕ) [Fact p.Prime] (hΔ : (E143Fp p).Δ ≠ 0)
    (x y : ZMod p) : Nonsingular (E143Fp p) x y ↔ E143_point p x y := by
  constructor
  · intro h
    exact (E143Fp_equation_iff p x y).mp h.1
  · intro h
    exact nonsingular_of_Δ_ne_zero (E143Fp p) ((E143Fp_equation_iff p x y).mpr h) hΔ

/-- Integral model of `(2, 0)`. -/
theorem E143Z_equation_two_zero : Equation E143Z 2 0 := by
  rw [equation_iff]
  dsimp [E143Z]

theorem E143Fp_nonsingular_two_zero (p : ℕ) [Fact p.Prime] (hΔ : (E143Fp p).Δ ≠ 0) :
    Nonsingular (E143Fp p) (2 : ZMod p) 0 :=
  nonsingular_of_Δ_ne_zero (E143Fp p)
    (Equation.map (Int.castRingHom (ZMod p)) E143Z_equation_two_zero) hΔ

/-- Reduction of the integral point `(2, 0)`. Not a map on `E(ℚ)`. -/
def BSD_reduce_two_zero (p : ℕ) [Fact p.Prime] (hΔ : (E143Fp p).Δ ≠ 0) :
    Point (E143Fp p) :=
  Point.some (E143Fp_nonsingular_two_zero p hΔ)

theorem BSD_reduce_two_zero_ne_zero (p : ℕ) [Fact p.Prime] (hΔ : (E143Fp p).Δ ≠ 0) :
    BSD_reduce_two_zero p hΔ ≠ 0 :=
  Point.some_ne_zero (E143Fp_nonsingular_two_zero p hΔ)

abbrev E143Sol (p : ℕ) [Fact p.Prime] := {xy : ZMod p × ZMod p // xy ∈ E143_Finset p}

def BSD_pointEquiv (p : ℕ) [Fact p.Prime] (hΔ : (E143Fp p).Δ ≠ 0) :
    Point (E143Fp p) ≃ Option (E143Sol p) where
  toFun
    | Point.zero => none
    | @Point.some _ _ _ x y h =>
        Option.some ⟨(x, y), by
          simp only [E143_Finset, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (E143Fp_nonsingular_iff p hΔ x y).mp h⟩
  invFun
    | none => Point.zero
    | Option.some ⟨(x, y), hm⟩ =>
        Point.some ((E143Fp_nonsingular_iff p hΔ x y).mpr <| by
          simpa [E143_Finset] using hm)
  left_inv
    | Point.zero => rfl
    | @Point.some _ _ _ x y h =>
        congr_arg (@Point.some (ZMod p) _ (E143Fp p) x y) (Subsingleton.elim _ _)
  right_inv
    | none => rfl
    | Option.some ⟨(x, y), hm⟩ => by
        apply congr_arg Option.some
        exact Subtype.ext rfl

theorem BSD_point_card_eq_affine_succ (p : ℕ) [Fact p.Prime] (hΔ : (E143Fp p).Δ ≠ 0) :
    Nat.card (Point (E143Fp p)) = (E143_Finset p).card + 1 := by
  let e := BSD_pointEquiv p hΔ
  haveI : Fintype (Point (E143Fp p)) := Fintype.ofEquiv _ e.symm
  haveI : Fintype (E143Sol p) := inferInstance
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_option, Fintype.card_coe]

theorem E143Fp_Δ_ne_zero_p3 : (E143Fp 3).Δ ≠ 0 :=
  E143Fp_Δ_ne_zero_of_not_dvd 3 E143Q_discriminant_not_div_by_2_3_5.2.1

theorem E143Fp_Δ_ne_zero_p5 : (E143Fp 5).Δ ≠ 0 :=
  E143Fp_Δ_ne_zero_of_not_dvd 5 E143Q_discriminant_not_div_by_2_3_5.2.2

theorem BSD_point_card_p3 : Nat.card (Point (E143Fp 3)) = 5 := by
  rw [BSD_point_card_eq_affine_succ 3 E143Fp_Δ_ne_zero_p3, BSD_E143_card_p3]

theorem BSD_point_card_p5 : Nat.card (Point (E143Fp 5)) = 7 := by
  rw [BSD_point_card_eq_affine_succ 5 E143Fp_Δ_ne_zero_p5, BSD_E143_card_p5]

/-- Injective homs into finite groups of coprime order force torsion to be `{0}`. -/
theorem BSD_torsion_trivial_of_coprime_cards
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {m n : ℕ}
    (hB : Nat.card B = m) (hC : Nat.card C = n) (hmn : Nat.gcd m n = 1)
    (f : ↥(AddCommGroup.torsion A) →+ B) (hf : Function.Injective f)
    (g : ↥(AddCommGroup.torsion A) →+ C) (hg : Function.Injective g)
    {a : A} (ha : IsOfFinAddOrder a) : a = 0 := by
  have hdivm : Nat.card (↥(AddCommGroup.torsion A)) ∣ m := by
    rw [← hB]
    exact AddSubgroup.card_dvd_of_injective f hf
  have hdivn : Nat.card (↥(AddCommGroup.torsion A)) ∣ n := by
    rw [← hC]
    exact AddSubgroup.card_dvd_of_injective g hg
  have hd : Nat.card (↥(AddCommGroup.torsion A)) ∣ Nat.gcd m n := Nat.dvd_gcd hdivm hdivn
  have hone : Nat.card (↥(AddCommGroup.torsion A)) = 1 := by
    rw [hmn] at hd
    exact Nat.eq_one_of_dvd_one hd
  obtain ⟨_z, hz⟩ := Nat.card_eq_one_iff_exists.mp hone
  have h0 : (0 : A) ∈ AddCommGroup.torsion A :=
    (AddCommGroup.mem_torsion A (0 : A)).2 isOfFinAddOrder_zero
  have ha' : a ∈ AddCommGroup.torsion A := (AddCommGroup.mem_torsion A a).2 ha
  have hsame : (⟨a, ha'⟩ : ↥(AddCommGroup.torsion A)) = ⟨0, h0⟩ := by
    rw [hz ⟨a, ha'⟩, hz ⟨0, h0⟩]
  exact congrArg Subtype.val hsame

/-- Rank lower bound from injective reduction-shaped maps into the Mathlib
    groups `E(𝔽₃)` and `E(𝔽₅)`, whose orders are the proved values `5` and `7`.
    The maps are hypotheses. -/
theorem BSD_rank_ge_one_of_reduction
    (f : ↥(AddCommGroup.torsion (Point E143Q)) →+ Point (E143Fp 3))
    (hf : Function.Injective f)
    (g : ↥(AddCommGroup.torsion (Point E143Q)) →+ Point (E143Fp 5))
    (hg : Function.Injective g) :
    Function.Injective (fun k : ℤ => k • E143Q_P20) := by
  refine BSD_Z_embedding_of_infinite_order ?_
  intro n hn hnP
  have ha : IsOfFinAddOrder E143Q_P20 :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hnP⟩
  have h0 : E143Q_P20 = 0 :=
    BSD_torsion_trivial_of_coprime_cards BSD_point_card_p3 BSD_point_card_p5
      (by decide) f hf g hg ha
  exact Point.some_ne_zero E143Q_nonsingular_two_zero h0

/-- The group orders and the reduction of `(2, 0)` are unconditional. The
    embedding of `ℤ` is not. `84 ≠ 54`. -/
theorem BSD_reduction_still_conditional :
    Nat.card (Point (E143Fp 3)) = (E143_Finset 3).card + 1 ∧
      Nat.card (Point (E143Fp 5)) = (E143_Finset 5).card + 1 ∧
      Nat.card (Point (E143Fp 3)) = 5 ∧
      Nat.card (Point (E143Fp 5)) = 7 ∧
      BSD_reduce_two_zero 3 E143Fp_Δ_ne_zero_p3 ≠ 0 ∧
      BSD_reduce_two_zero 5 E143Fp_Δ_ne_zero_p5 ≠ 0 ∧
      (84 : ℕ) ≠ 54 := by
  exact ⟨BSD_point_card_eq_affine_succ 3 E143Fp_Δ_ne_zero_p3,
    BSD_point_card_eq_affine_succ 5 E143Fp_Δ_ne_zero_p5,
    BSD_point_card_p3, BSD_point_card_p5,
    BSD_reduce_two_zero_ne_zero 3 E143Fp_Δ_ne_zero_p3,
    BSD_reduce_two_zero_ne_zero 5 E143Fp_Δ_ne_zero_p5,
    BSD_54_of_504.2.2⟩

end Towers.BSD
