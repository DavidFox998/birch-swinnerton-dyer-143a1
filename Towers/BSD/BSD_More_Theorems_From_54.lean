/-
  Five theorems packed from proofs that already compile.
  No new `E143_Finset` enumeration. No sorry.
  The assessed tally stays 54 of 504. These are corollaries.
  They do not prove Hasse for every prime, modularity, the L-series bound
  for every n, class number 10, or that (2, 0) is non-torsion.
-/

import Towers.BSD.BSD_Finite_Hasse_54_Theorem
import BSD_Assessed_Batch1
import BSD_Assessed_Batch2
import BSD_Assessed_Batch3
import BSD_Assessed_Batch4
import BSD_Assessed_Batch5
import BSD_Assessed_Batch6
import BSD_Assessed_Batch7
import BSD_Assessed_Batch8
import BSD_Assessed_Batch9
import BSD_Assessed_Batch10

open BSD_MissingDefinitionsRegistry

namespace Towers.BSD

/-! ## 1. Both Hasse forms on the 84 checked primes -/

/-- The Batch 3 algebra, for one prime. The quantified theorem
    `BSD_RamanujanBound_iff_Discriminant_prop` equates two statements
    about every good prime. Neither of those is proved. This direction
    is the same square comparison, with the quantifiers removed. -/
theorem BSD_Hasse_forms_pointwise (p : ℕ) [Fact p.Prime] :
    |(a_p p : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) ↔ (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  constructor
  · intro hram
    have hp_nn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    have habs_sq : |(a_p p : ℝ)| ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 :=
      sq_le_sq' (by linarith [abs_nonneg (a_p p : ℝ)]) hram
    rw [sq_abs, mul_pow, Real.sq_sqrt hp_nn] at habs_sq
    linarith
  · intro hd
    have hp_nn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    have h2nn : (0 : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by positivity
    calc |(a_p p : ℝ)|
        = Real.sqrt ((a_p p : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (4 * (p : ℝ)) := Real.sqrt_le_sqrt hd
      _ = 2 * Real.sqrt (p : ℝ) := by
          rw [show (4 : ℝ) * (p : ℝ) = (2 * Real.sqrt (p : ℝ)) ^ 2 from by
                rw [mul_pow, Real.sq_sqrt hp_nn]; norm_num]
          exact Real.sqrt_sq h2nn

/-- Both forms for each compiled prime. Cites `BSD_Finite_Hasse_54_proved`.
    Does not prove either form for every prime. -/
theorem BSD_Hasse_Forms_Equiv_84
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    |(a_p p : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) ∧ (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hHasse : BSD_Hasse_OPEN p := (BSD_Finite_Hasse_54_proved p hp).2.1
  exact ⟨hHasse, (BSD_Hasse_forms_pointwise p).mp hHasse⟩

/-! ## 2. Coprime multiplicativity at two checked primes -/

lemma a_n_eq_a_p (p : ℕ) [Fact p.Prime] : a_n p = a_p p := by
  conv_lhs => rw [← Nat.pow_one p]
  rw [a_n_prime_pow p 1]
  rfl

/-- `a_n` is multiplicative on coprime arguments. This is the Batch 3 theorem.
    The values below use the compiled counts `a_p 251 = 21` and `a_p 257 = 18`.
    `251 * 257 = 64507` and `21 * 18 = 378`. Not modularity. -/
theorem BSD_Coprime_Multiplicativity_Applies_84 :
    a_n (251 * 257) = a_n 251 * a_n 257 ∧
      a_n 251 = 21 ∧ a_n 257 = 18 ∧
      251 * 257 = 64507 ∧ a_n 64507 = 378 := by
  have hmul :=
    Towers_BSD_BSD_Multiplicativity_Closed_Assessed.BSD_HeckeMultiplicativity_143_CLOSED_prop
      251 257 (by decide)
  have h251 : a_n 251 = 21 := by rw [a_n_eq_a_p 251, BSD_ap_p251]
  have h257 : a_n 257 = 18 := by rw [a_n_eq_a_p 257, BSD_ap_p257]
  have hprod : (21 : ℤ) * 18 = 378 := by decide
  have hN : 251 * 257 = 64507 := by decide
  refine ⟨hmul, h251, h257, hN, ?_⟩
  rw [← hN, hmul, h251, h257, hprod]

/-! ## 3. Weierstrass coefficients and the affine point (2, 0) -/

lemma E143_affine_two_zero (p : ℕ) [Fact p.Prime] :
    E143_point p (2 : ZMod p) 0 := by
  simp only [E143_point]
  ring

lemma E143_affine_two_zero_mem (p : ℕ) [Fact p.Prime] :
    ((2 : ZMod p), (0 : ZMod p)) ∈ E143_Finset p := by
  rw [E143_Finset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, E143_affine_two_zero p⟩

/-- Coefficients `(0, -1, 1, -1, -2)`, the rational point `(2, 0)`, and the
    same point on the affine model over each checked prime. The identity
    `0 = 8 - 4 - 2 - 2` holds in `ZMod p`. Not non-torsion, not a generator,
    not rank 1, not BSD. `BSD_HeegnerPoint_OPEN` stays the registry `True`. -/
theorem BSD_Weierstrass_Coeff_Affine_Point_Theorem
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₁ = 0 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₂ = -1 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₃ = 1 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₄ = -1 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₆ = -2 ∧
      (∃ x y : ℚ, y ^ 2 + y = x ^ 3 - x ^ 2 - x - 2) ∧
      ((2 : ZMod p), (0 : ZMod p)) ∈ E143_Finset p ∧
      p < 1000 := by
  have h := Towers_BSD_E143a1_CLOSED_Assessed.E143a1_prop
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
    Towers_BSD_E143a1_CLOSED_Assessed.E143a1_has_rational_point_prop,
    E143_affine_two_zero_mem p,
    BSD_Finite_Hasse_CheckedPrimes_lt_1000 hp⟩

/-! ## 4. The three Batch 1 theorems, still short of class number -/

/-- Minkowski bound, the four-`True` decomposition, and the implication ledger.
    Class number `10 ≤ h(K)` and `h(K) ≤ 10` stay NEEDS_AUTHORING.
    The upper bound needs `BinaryQuadraticForm.classGroupEquiv`, absent from
    Mathlib v4.12.0. The ledger does not discharge the empirical `a_p` props. -/
theorem BSD_Minkowski_H1_AP_Ledger_Theorem :
    (2 / Real.pi * Real.sqrt 143 < 8) ∧
      (True ∧ True ∧ True ∧ True) ∧
      ((BSD_ap11_card_EMPIRICAL → False → False) ∧
        (BSD_ap13_card_EMPIRICAL → False → False) ∧
        (BSD_ap17_card_EMPIRICAL → False → False) ∧
        (BSD_ap19_card_EMPIRICAL → False → False) ∧
        (BSD_ap23_card_EMPIRICAL → False → False) ∧
        (BSD_ap29_card_EMPIRICAL → False → False) ∧
        (BSD_ap191_card_EMPIRICAL → False → False)) :=
  ⟨Towers_BSD_BSD_ClassNumberBounds_Assessed.BSD_minkowski_lt_8_prop,
    Towers_BSD_BSD_AnalyticRank_Assessed.BSD_H1_decomp_verified_prop,
    Towers_BSD_BSD_AP_Table_Assessed.BSD_AP_surface_ledger_prop⟩

/-! ## 5. The coefficient bound still a hypothesis -/

/-- Batch 4, cited again by Batch 10: a bound on every `a_n` implies
    summability for `Re(s) > 3/2`. Each checked prime satisfies `|a_p| ≤ 2√p`.
    Those 84 inequalities are not a bound for every `n`, so this does not
    discharge summability of the L-series. -/
theorem BSD_Coefficient_Bound_Implies_Summability_54
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    ((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ+,
        |(a_n n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε)) →
      (∀ s : ℂ, 3 / 2 < s.re →
        Summable fun n : ℕ+ => (a_n n : ℂ) / (n : ℂ) ^ s)) ∧
      |(a_p p : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) :=
  ⟨hasseprimset_BSD_Finsupp_prod_le_close_Assessed.BSD_isBigO_to_LSeries_close_prop,
    (BSD_Hasse_Forms_Equiv_84 p hp).1⟩

end Towers.BSD
