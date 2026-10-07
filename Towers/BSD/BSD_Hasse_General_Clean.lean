/-
  Partial Group A. The 84 checked primes, not Hasse for every prime.

  Mathlib v4.12.0 `AlgebraicGeometry/EllipticCurve` contains Affine,
  DivisionPolynomial, Group, Jacobian, Projective, VariableChange, and
  Weierstrass. A search of those files finds no `Hasse` and no `Frobenius`.
  There is no elliptic Hasse theorem to cite.

  The degree form `r² − a_p r + p ≥ 0` is already compiled for each of the
  84 checked primes. `BSD_hasse_of_degree_nonneg` turns that form into
  `|a_p| ≤ 2√p`. `BSD_Hasse_forms_pointwise` is the Batch 3 square comparison
  with the quantifiers removed. Together they give the equivalence on the
  checked set.

  `∀ p [Fact p.Prime], ¬ p ∣ 143 → a_p² ≤ 4p` stays NEEDS_AUTHORING.
  Counts through 983 do not prove that forall. `E143_Finset 9973` is not
  evaluated here. A general proof is the Hasse argument in Silverman,
  AEC §V.2, which is not in this file.

  No new point count. No prime at or above 1000. No sorry.
-/

import Towers.BSD.BSD_More_Theorems_From_54

namespace Towers.BSD

/-- For each of the 84 checked primes, the compiled degree form gives
    `a_p² ≤ 4p`. Cites `BSD_Finite_Hasse_54_proved`, then
    `BSD_hasse_of_degree_nonneg`, then the Batch 3 square comparison.
    Does not re-enumerate `E143_Finset`. -/
lemma BSD_Hasse_degree_nonneg
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hdeg : BSD_FrobeniusDegreeNonneg_OPEN p :=
    (BSD_Finite_Hasse_54_proved p hp).1
  have hHasse : BSD_Hasse_OPEN p := BSD_hasse_of_degree_nonneg p hdeg
  exact (BSD_Hasse_forms_pointwise p).mp hHasse

/-- On the checked set, `|a_p| ≤ 2√p` is the square bound together with the
    degree form. The degree form is the compiled `BSD_FrobeniusDegreeNonneg_OPEN`.
    The square comparison is `BSD_Hasse_forms_pointwise`.
    This is not Hasse for every good prime. -/
theorem BSD_Hasse_for_checked_is_degree_form
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    |(a_p p : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) ↔
      (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) ∧ BSD_FrobeniusDegreeNonneg_OPEN p := by
  have hdeg : BSD_FrobeniusDegreeNonneg_OPEN p :=
    (BSD_Finite_Hasse_54_proved p hp).1
  constructor
  · intro habs
    exact ⟨(BSD_Hasse_forms_pointwise p).mp habs, hdeg⟩
  · rintro ⟨_, hdeg'⟩
    exact BSD_hasse_of_degree_nonneg p hdeg'

/-- Enumeration through 983 does not prove `a_p² ≤ 4p` for every good prime.
    983² = 966289 affine pairs, and that count is already compiled.
    9973² = 99460729 affine pairs. This file does not evaluate
    `E143_Finset 9973`. 9973 is prime, does not divide 143, and lies outside
    the checked set. 11 and 13 divide 143 and lie outside it.
    The forall stays NEEDS_AUTHORING. The gate is the missing Hasse theorem
    in Mathlib v4.12.0. -/
theorem BSD_Hasse_forall_needs_general :
    BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      (∀ p ∈ BSD_Finite_Hasse_CheckedPrimes, p < 1000) ∧
      983 ∈ BSD_Finite_Hasse_CheckedPrimes ∧
      983 * 983 = 966289 ∧
      9973 * 9973 = 99460729 ∧
      Nat.Prime 9973 ∧ ¬ (9973 ∣ 143) ∧
      9973 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      11 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      13 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      11 ∣ 143 ∧ 13 ∣ 143 ∧
      (84 : ℕ) ≠ 54 := by
  have hceil := BSD_Ceiling_Theorem
  refine ⟨BSD_Finite_Hasse_CheckedPrimes_card,
      fun _ hp => BSD_Finite_Hasse_CheckedPrimes_lt_1000 hp,
      ?_, by decide, by decide,
      hceil.1, hceil.2.1, hceil.2.2.1, hceil.2.2.2.1, hceil.2.2.2.2.1,
      hceil.2.2.2.2.2.1, hceil.2.2.2.2.2.2.1, BSD_54_of_504.2.2⟩
  have h983 : 983 ∈ BSD_Finite_Hasse_CheckedList := by decide
  simpa [BSD_Finite_Hasse_CheckedPrimes] using h983

end Towers.BSD
