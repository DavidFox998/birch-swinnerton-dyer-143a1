/-
  Partial Group F, continued. Counts at 2, 3, and 5, and the group-theory
  step of a rank lower bound.

  The Weierstrass discriminant of `[0, -1, 1, -1, -2]` is `-1859 = -(11 * 13^2)`.
  It is not the field discriminant `-143`. The primes 2, 3, and 5 do not divide
  `1859`. The affine counts already compiled are 2, 4, and 6, so the integers
  `affine.card + 1` are 3, 5, and 7. Those three integers are pairwise coprime.
  They are the Hasse normalization `p + 1 - a_p`. This file does not construct
  the group `E(𝔽_p)`.

  Nagell–Lutz does not exclude `(2, 0)`: `2y + a₃ = 1`, and `1` divides `1859`.

  If the torsion subgroup admits injective homomorphisms into `ZMod 5` and
  `ZMod 7`, Lagrange forces it to be `{0}`, so `(2, 0)` has infinite order and
  `ℤ` embeds into the rational points. Those homomorphisms are what Silverman's
  reduction theorem would give for the odd primes 3 and 5. Mathlib v4.12.0 has
  no reduction map `E(ℚ) → E(𝔽_p)`. At `p = 2` the classical injection sees only
  the odd-order torsion, so coprimeness of the counts 3 and 5 is not that theorem.
  Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, the regulator, Néron–Tate
  height, rank exactly 1, and the BSD formula stay NEEDS_AUTHORING.
  The 54 assessed definitions were not rewritten. No new point count. No sorry.
-/

import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.ZMod.Basic
import Towers.BSD.BSD_TorsionOrder_Clean
import Towers.BSD.BSD_Hasse_Points_2_7

open WeierstrassCurve WeierstrassCurve.Affine

namespace Towers.BSD

theorem E143Q_discriminant : E143Q.Δ = -(1859 : ℚ) := by
  simp only [E143Q, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

theorem E143Q_discriminant_factors : (1859 : ℕ) = 11 * 13 ^ 2 := by
  norm_num

/-- `2`, `3`, and `5` do not divide the curve discriminant. -/
theorem E143Q_discriminant_not_div_by_2_3_5 :
    ¬ (2 : ℕ) ∣ 1859 ∧ ¬ (3 : ℕ) ∣ 1859 ∧ ¬ (5 : ℕ) ∣ 1859 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The Nagell–Lutz quantity at `(2, 0)` is `1`, which divides `1859`. -/
theorem BSD_nagell_lutz_quantity_divides :
    (2 * (0 : ℚ) + E143Q.a₁ * 2 + E143Q.a₃) = 1 ∧ (1 : ℤ) ∣ 1859 := by
  constructor
  · dsimp [E143Q]
    norm_num
  · exact one_dvd _

theorem BSD_affine_card_plus_one_2_3_5 :
    (E143_Finset 2).card + 1 = 3 ∧
      (E143_Finset 3).card + 1 = 5 ∧
      (E143_Finset 5).card + 1 = 7 ∧
      Nat.gcd 3 5 = 1 ∧ Nat.gcd 5 7 = 1 ∧ Nat.gcd 3 7 = 1 := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide⟩
  · rw [BSD_E143_card_p2]
  · rw [BSD_E143_card_p3]
  · rw [BSD_E143_card_p5]

/-- Two injective homs into additive groups of coprime finite order force the
    torsion subgroup to be `{0}`. -/
theorem BSD_torsion_trivial_of_coprime_injections
    {A : Type*} [AddCommGroup A] {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : Nat.gcd m n = 1)
    (f : ↥(AddCommGroup.torsion A) →+ ZMod m) (hf : Function.Injective f)
    (g : ↥(AddCommGroup.torsion A) →+ ZMod n) (hg : Function.Injective g)
    {a : A} (ha : IsOfFinAddOrder a) : a = 0 := by
  have hcardm : Nat.card (ZMod m) = m := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hcardn : Nat.card (ZMod n) = n := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hdivm : Nat.card (↥(AddCommGroup.torsion A)) ∣ m := by
    rw [← hcardm]
    exact AddSubgroup.card_dvd_of_injective f hf
  have hdivn : Nat.card (↥(AddCommGroup.torsion A)) ∣ n := by
    rw [← hcardn]
    exact AddSubgroup.card_dvd_of_injective g hg
  have hd : Nat.card (↥(AddCommGroup.torsion A)) ∣ Nat.gcd m n :=
    Nat.dvd_gcd hdivm hdivn
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

/-- Infinite order gives an embedding of `ℤ`. -/
theorem BSD_Z_embedding_of_infinite_order
    (hinf : ∀ n : ℕ, 0 < n → n • E143Q_P20 ≠ 0) :
    Function.Injective (fun k : ℤ => k • E143Q_P20) := by
  intro a b hab
  have hab' : a • E143Q_P20 = b • E143Q_P20 := hab
  have hdiff : (a - b) • E143Q_P20 = 0 := by
    rw [sub_zsmul, hab', add_neg_cancel]
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  rcases lt_trichotomy (a - b) 0 with hlt | heq | hgt
  · have hpos : 0 < b - a := by
      rw [← neg_sub]
      exact neg_pos.mpr hlt
    have hsmash : (b - a) • E143Q_P20 = 0 := by
      rw [← neg_sub a b, neg_zsmul, hdiff, neg_zero]
    have hn : 0 < (b - a).toNat :=
      Int.natCast_pos.mp ((Int.toNat_of_nonneg hpos.le).symm ▸ hpos)
    have hnat : ((b - a).toNat) • E143Q_P20 = 0 := by
      rw [← natCast_zsmul, Int.toNat_of_nonneg hpos.le]
      exact hsmash
    exact hinf _ hn hnat
  · exact hsub heq
  · have hn : 0 < (a - b).toNat :=
      Int.natCast_pos.mp ((Int.toNat_of_nonneg hgt.le).symm ▸ hgt)
    have hnat : ((a - b).toNat) • E143Q_P20 = 0 := by
      rw [← natCast_zsmul, Int.toNat_of_nonneg hgt.le]
      exact hdiff
    exact hinf _ hn hnat

/-- Conditional rank lower bound. The maps into `ZMod 5` and `ZMod 7` are the
    shape of reduction at the odd primes `3` and `5`, whose `affine.card + 1`
    values are `5` and `7`. The maps themselves are not constructed. -/
theorem BSD_rank_ge_one_of_torsion_injection
    (f : ↥(AddCommGroup.torsion (Point E143Q)) →+ ZMod 5) (hf : Function.Injective f)
    (g : ↥(AddCommGroup.torsion (Point E143Q)) →+ ZMod 7) (hg : Function.Injective g) :
    Function.Injective (fun k : ℤ => k • E143Q_P20) := by
  refine BSD_Z_embedding_of_infinite_order ?_
  intro n hn hnP
  have ha : IsOfFinAddOrder E143Q_P20 :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hnP⟩
  have h0 : E143Q_P20 = 0 :=
    BSD_torsion_trivial_of_coprime_injections (by decide : Nat.gcd 5 7 = 1) f hf g hg ha
  exact Point.some_ne_zero E143Q_nonsingular_two_zero h0

/-- Requested name for the conditional embedding. The maps into `ZMod 5` and
    `ZMod 7` are hypotheses, not a constructed reduction `E(ℚ) → E(𝔽_p)`. -/
theorem BSD_rank_ge_one
    (f : ↥(AddCommGroup.torsion (Point E143Q)) →+ ZMod 5) (hf : Function.Injective f)
    (g : ↥(AddCommGroup.torsion (Point E143Q)) →+ ZMod 7) (hg : Function.Injective g) :
    Function.Injective (fun k : ℤ => k • E143Q_P20) :=
  BSD_rank_ge_one_of_torsion_injection f hf g hg

/-- The conditional embedding is not Gross–Zagier, Kolyvagin, or BSD.
    The registry torsion count stays the constant `1`. `84 ≠ 54`. -/
theorem BSD_rank_ge_one_not_bsd :
    (2 : ℕ) • E143Q_P20 ≠ 0 ∧
      (E143_Finset 3).card + 1 = 5 ∧
      (E143_Finset 5).card + 1 = 7 ∧
      Nat.gcd 5 7 = 1 ∧
      E143Q.Δ = -(1859 : ℚ) ∧
      BSD_MissingDefinitionsRegistry.BSD_TorsCard = 1 ∧
      (84 : ℕ) ≠ 54 := by
  exact ⟨BSD_affine_not_two_torsion, by rw [BSD_E143_card_p3], by rw [BSD_E143_card_p5],
    by decide, E143Q_discriminant, rfl, BSD_54_of_504.2.2⟩

end Towers.BSD
