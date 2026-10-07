/-
  Partial Group A, continued. The degree form implies the square bound.

  Mathlib v4.12.0 `AlgebraicGeometry/EllipticCurve` has no Frobenius
  endomorphism and no Hasse theorem. This file does not define the
  Frobenius of `E(𝔽_p)` and does not prove
  `∀ p [Fact p.Prime], ¬ p ∣ 143 → a_p² ≤ 4p`.

  `BSD_FrobeniusDegreeNonneg_OPEN p` is the quadratic
  `∀ r, r² − a_p r + p ≥ 0`. Where that hypothesis is known,
  `BSD_hasse_of_degree_nonneg` and `BSD_Hasse_forms_pointwise` give
  `a_p² ≤ 4p`. The hypothesis is compiled for the 84 checked primes.
  It is not compiled for every good prime. Proving the hypothesis in
  general is Silverman AEC §V.2, and it is not in this file.

  The 328 assessed definitions were not rewritten. No new point count.
  No prime at or above 1000. No sorry.
-/

import Towers.BSD.BSD_Hasse_General_Clean

namespace Towers.BSD

/-- For an arbitrary prime, the degree form implies `a_p² ≤ 4p`.
    The hypothesis is not proved for every good prime. -/
theorem BSD_Hasse_square_of_degree
    (p : ℕ) [Fact p.Prime] (h : BSD_FrobeniusDegreeNonneg_OPEN p) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) :=
  (BSD_Hasse_forms_pointwise p).mp (BSD_hasse_of_degree_nonneg p h)

/-- The checked set is not every good prime, so the degree form on that set
    does not prove the forall. 9973 is prime, does not divide 143, and is
    outside the set. 11 and 13 divide 143 and are outside. This file does
    not evaluate `E143_Finset 9973`. -/
theorem BSD_Hasse_forall_not_from_checked :
    BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      (∀ p ∈ BSD_Finite_Hasse_CheckedPrimes, p < 1000) ∧
      Nat.Prime 9973 ∧ ¬ (9973 ∣ 143) ∧
      9973 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      11 ∣ 143 ∧ 13 ∣ 143 ∧
      11 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      13 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      (84 : ℕ) ≠ 54 := by
  have hceil := BSD_Ceiling_Theorem
  exact ⟨BSD_Finite_Hasse_CheckedPrimes_card,
    fun _ hp => BSD_Finite_Hasse_CheckedPrimes_lt_1000 hp,
    hceil.1, hceil.2.1, hceil.2.2.1,
    hceil.2.2.2.2.2.1, hceil.2.2.2.2.2.2.1,
    hceil.2.2.2.1, hceil.2.2.2.2.1,
    BSD_54_of_504.2.2⟩

end Towers.BSD
