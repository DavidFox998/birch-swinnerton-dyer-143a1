/-
  Group A, rewritten under the clean names.

  `BSD_Frobenius_degree_nonneg` is the degree form already used in the clean
  build: `∀ r, r² − a_p r + p ≥ 0`. Where it holds, `BSD_Hasse_bound_of_degree`
  gives `a_p² ≤ 4p`. `BSD_Hasse_bound_forall` is that implication for every
  prime outside the primes dividing `1859`.

  The degree form is a hypothesis. It is compiled for the 84 checked primes.
  Mathlib v4.12.0 has no Frobenius endomorphism of an elliptic curve and no
  Hasse theorem. This file does not define `degree_frobenius` and does not
  set that degree equal to `p`.

  A prime divides `143 = 11 * 13` if and only if it divides
  `1859 = 11 * 13²`. Good reduction for this model is the same set of primes
  as the conductor condition. The forall over that set stays conditional.

  The 328 assessed definitions were not rewritten. No new point count.
  No prime at or above 1000. No sorry.
-/

import Towers.BSD.BSD_Frobenius_Clean
import Towers.BSD.BSD_RankAtLeastOne_Clean

namespace Towers.BSD

/-- The degree form. Not a proof that the form is nonnegative. -/
def BSD_Frobenius_degree_nonneg (p : ℕ) [Fact p.Prime] : Prop :=
  BSD_FrobeniusDegreeNonneg_OPEN p

/-- The degree form implies the square bound, for one prime. -/
theorem BSD_Hasse_bound_of_degree
    (p : ℕ) [Fact p.Prime] (h : BSD_Frobenius_degree_nonneg p) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) :=
  BSD_Hasse_square_of_degree p h

/-- Same square bound for every prime not dividing `1859`, given the degree
    form at every such prime. -/
theorem BSD_Hasse_bound_forall
    (hdeg : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 1859 → BSD_Frobenius_degree_nonneg p)
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 1859) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) :=
  BSD_Hasse_bound_of_degree p (hdeg p hp)

/-- The primes of bad reduction are `11` and `13`, for both `143` and `1859`. -/
theorem BSD_prime_dvd_143_iff_dvd_1859 (p : ℕ) (hp : Nat.Prime p) :
    p ∣ 143 ↔ p ∣ 1859 := by
  have h143 : 143 = 11 * 13 := by decide
  have h1859 : (1859 : ℕ) = 11 * 13 ^ 2 := E143Q_discriminant_factors
  rw [h143, h1859]
  constructor
  · intro h
    rcases hp.dvd_mul.mp h with h11 | h13
    · exact dvd_mul_of_dvd_left h11 _
    · exact dvd_mul_of_dvd_right (dvd_pow h13 (by decide)) _
  · intro h
    rcases hp.dvd_mul.mp h with h11 | h13sq
    · exact dvd_mul_of_dvd_left h11 _
    · exact dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h13sq) _

/-- The checked set has 84 primes, all below 1000. It is not every prime
    outside `{11, 13}`. `84 ≠ 54`. -/
theorem BSD_Hasse_forall_still_conditional :
    BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      (∀ q ∈ BSD_Finite_Hasse_CheckedPrimes, q < 1000) ∧
      (∀ p : ℕ, Nat.Prime p → (p ∣ 143 ↔ p ∣ 1859)) ∧
      (84 : ℕ) ≠ 54 :=
  ⟨BSD_Hasse_forall_not_from_checked.1,
    BSD_Hasse_forall_not_from_checked.2.1,
    BSD_prime_dvd_143_iff_dvd_1859,
    BSD_54_of_504.2.2⟩

end Towers.BSD
