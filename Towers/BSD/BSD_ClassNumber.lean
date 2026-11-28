import Towers.BSD.BSD_NumberField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Data.ZMod.Basic

/-
  # BSD_ClassNumber — Norm-form certificates for h(ℚ(√-143)) = 10

  Standalone re-declaration of the K1ClassNumber arithmetic under Towers.BSD.
  This file mirrors Towers.RH.JorgensonKramer.X0_143.K1ClassNumber but imports
  only from BSD_NumberField (no Towers.RH.* imports).

  FULLY PROVED IN THIS FILE (sorry = 0, axiom footprint = classical trio):
    norm_form_no_norm_two_BSD     no a b : ℤ with a²+ab+36b² = 2
    norm_form_no_norm_eight_BSD   no a b : ℤ with a²+ab+36b² = 8
    norm_form_no_norm_32_BSD      no a b : ℤ with a²+ab+36b² = 32
    norm_form_no_norm_128_BSD     no a b : ℤ with a²+ab+36b² = 128
    norm_form_no_norm_512_BSD     no a b : ℤ with a²+ab+36b² = 512
    norm_form_no_norm_three_BSD   no a b : ℤ with a²+ab+36b² = 3
    norm_form_no_norm_seven_BSD   no a b : ℤ with a²+ab+36b² = 7
    norm_form_gen_1024_BSD        (-28)²+(-28)·3+36·3² = 1024
    prime_2_splits_BSD            X²−X+36 ≡ 0 (mod 2) is solvable
    prime_3_splits_BSD            X²−X+36 ≡ 0 (mod 3) is solvable
    prime_5_inert_BSD             X²−X+36 ≡ 0 (mod 5) is not solvable
    prime_7_splits_BSD            X²−X+36 ≡ 0 (mod 7) is solvable

  OPEN SURFACES (def Prop — not sorry, not axiom):
    K1_ClassNumber_Upper_BSD      classNumber K ≤ 10
    K1_ClassNumber_Lower_BSD      10 ≤ classNumber K

  COMBINATOR (0 sorry, classical trio):
    K1_ClassNumber_Certificate_BSD   classNumber K = 10  (conditional)

  SORRY: 0. Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
-/

namespace Towers.BSD

open NumberField Real FiniteDimensional

/-! ### Step 1: Helper for norm-form proofs -/

lemma one_le_sq_of_ne_zero_BSD {n : ℤ} (hn : n ≠ 0) : 1 ≤ n ^ 2 := by
  rcases lt_or_gt_of_ne hn with h | h
  · have hle : n ≤ -1 := Int.le_sub_one_of_lt h
    nlinarith [sq_nonneg (n + 1)]
  · nlinarith [sq_nonneg (n - 1)]

/-! ### Step 2: Norm-form impossibilities (odd powers of 2) -/

/-- No a b : ℤ satisfy a² + ab + 36b² = 2. -/
lemma norm_form_no_norm_two_BSD (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 2 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 8 := by linear_combination 4 * h
  have hb : b = 0 := by
    by_contra hb'
    nlinarith [one_le_sq_of_ne_zero_BSD hb', sq_nonneg (2 * a + b)]
  subst hb; simp only [mul_zero, add_zero] at h
  have ha_le : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have ha_ge : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
  interval_cases a <;> simp_all

/-- No a b : ℤ satisfy a² + ab + 36b² = 8. -/
lemma norm_form_no_norm_eight_BSD (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 8 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 32 := by linear_combination 4 * h
  have hb : b = 0 := by
    by_contra hb'
    nlinarith [one_le_sq_of_ne_zero_BSD hb', sq_nonneg (2 * a + b)]
  subst hb; simp only [mul_zero, add_zero] at h
  have ha_le : a ≤ 2 := by nlinarith [sq_nonneg (a - 3)]
  have ha_ge : -2 ≤ a := by nlinarith [sq_nonneg (a + 3)]
  interval_cases a <;> simp_all

/-- No a b : ℤ satisfy a² + ab + 36b² = 32. -/
lemma norm_form_no_norm_32_BSD (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 32 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 128 := by linear_combination 4 * h
  have hb : b = 0 := by
    by_contra hb'
    nlinarith [one_le_sq_of_ne_zero_BSD hb', sq_nonneg (2 * a + b)]
  subst hb; simp only [mul_zero, add_zero] at h
  have ha_le : a ≤ 5 := by nlinarith [sq_nonneg (a - 6)]
  have ha_ge : -5 ≤ a := by nlinarith [sq_nonneg (a + 6)]
  interval_cases a <;> simp_all

/-- No a b : ℤ satisfy a² + ab + 36b² = 128. -/
lemma norm_form_no_norm_128_BSD (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 128 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 512 := by linear_combination 4 * h
  have hb1 : b ^ 2 ≤ 3 := by nlinarith [sq_nonneg (2 * a + b)]
  have hble : b ≤ 1 := by nlinarith [sq_nonneg (b - 2)]
  have hbge : -1 ≤ b := by nlinarith [sq_nonneg (b + 2)]
  have h_bnd : (2 * a + b) ^ 2 ≤ 512 := by nlinarith [sq_nonneg b]
  have h_le : 92 * a ≤ 1087 := by nlinarith [sq_nonneg (2 * a + b - 23), h_bnd, hbge]
  have ha_le : a ≤ 11 := by omega
  have h_ge : -1087 ≤ 92 * a := by nlinarith [sq_nonneg (2 * a + b + 23), h_bnd, hble]
  have ha_ge : -11 ≤ a := by omega
  interval_cases b <;> interval_cases a <;> norm_num at h

/-- No a b : ℤ satisfy a² + ab + 36b² = 512. -/
lemma norm_form_no_norm_512_BSD (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 512 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 2048 := by linear_combination 4 * h
  have hb2 : b ^ 2 ≤ 14 := by nlinarith [sq_nonneg (2 * a + b)]
  have hble : b ≤ 3 := by nlinarith [sq_nonneg (b - 4)]
  have hbge : -3 ≤ b := by nlinarith [sq_nonneg (b + 4)]
  interval_cases b
  · have h' : a ^ 2 - 3 * a - 188 = 0 := by linarith
    have ha_le : a ≤ 16 := by nlinarith [sq_nonneg (a - 17)]
    have ha_ge : -13 ≤ a := by nlinarith [sq_nonneg (a + 14)]
    interval_cases a <;> omega
  · have h' : a ^ 2 - 2 * a - 368 = 0 := by linarith
    have ha_le : a ≤ 20 := by nlinarith [sq_nonneg (a - 21)]
    have ha_ge : -18 ≤ a := by nlinarith [sq_nonneg (a + 19)]
    interval_cases a <;> omega
  · have h' : a ^ 2 - a - 476 = 0 := by linarith
    have ha_le : a ≤ 22 := by nlinarith [sq_nonneg (a - 23)]
    have ha_ge : -21 ≤ a := by nlinarith [sq_nonneg (a + 22)]
    interval_cases a <;> omega
  · simp only [mul_zero, add_zero] at h
    have ha_le : a ≤ 22 := by nlinarith [sq_nonneg (a - 23)]
    have ha_ge : -22 ≤ a := by nlinarith [sq_nonneg (a + 23)]
    interval_cases a <;> simp_all
  · have h' : a ^ 2 + a - 476 = 0 := by linarith
    have ha_le : a ≤ 21 := by nlinarith [sq_nonneg (a - 22)]
    have ha_ge : -22 ≤ a := by nlinarith [sq_nonneg (a + 22)]
    interval_cases a <;> omega
  · have h' : a ^ 2 + 2 * a - 368 = 0 := by linarith
    have ha_le : a ≤ 18 := by nlinarith [sq_nonneg (a - 19)]
    have ha_ge : -20 ≤ a := by nlinarith [sq_nonneg (a + 20)]
    interval_cases a <;> omega
  · have h' : a ^ 2 + 3 * a - 188 = 0 := by linarith
    have ha_le : a ≤ 13 := by nlinarith [sq_nonneg (a - 14)]
    have ha_ge : -16 ≤ a := by nlinarith [sq_nonneg (a + 16)]
    interval_cases a <;> omega

/-! ### Step 3: Norm-form impossibilities for primes 3 and 7 -/

/-- No a b : ℤ satisfy a² + ab + 36b² = 3. -/
lemma norm_form_no_norm_three_BSD (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 3 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 12 := by linear_combination 4 * h
  have hb : b = 0 := by
    by_contra hb'
    nlinarith [one_le_sq_of_ne_zero_BSD hb', sq_nonneg (2 * a + b)]
  subst hb; simp only [mul_zero, add_zero] at h
  have ha_le : a ≤ 1 := by nlinarith [sq_nonneg (a - 2)]
  have ha_ge : -1 ≤ a := by nlinarith [sq_nonneg (a + 2)]
  interval_cases a <;> simp_all

/-- No a b : ℤ satisfy a² + ab + 36b² = 5. -/
lemma norm_form_no_norm_five_BSD (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 5 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 20 := by linear_combination 4 * h
  have hb : b = 0 := by
    by_contra hb'
    nlinarith [one_le_sq_of_ne_zero_BSD hb', sq_nonneg (2 * a + b)]
  subst hb; simp only [mul_zero, add_zero] at h
  have ha_le : a ≤ 2 := by nlinarith [sq_nonneg (a - 3)]
  have ha_ge : -2 ≤ a := by nlinarith [sq_nonneg (a + 3)]
  interval_cases a <;> simp_all

/-- No a b : ℤ satisfy a² + ab + 36b² = 7. -/
lemma norm_form_no_norm_seven_BSD (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 7 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 28 := by linear_combination 4 * h
  have hb : b = 0 := by
    by_contra hb'
    nlinarith [one_le_sq_of_ne_zero_BSD hb', sq_nonneg (2 * a + b)]
  subst hb; simp only [mul_zero, add_zero] at h
  have ha_le : a ≤ 2 := by nlinarith [sq_nonneg (a - 3)]
  have ha_ge : -2 ≤ a := by nlinarith [sq_nonneg (a + 3)]
  interval_cases a <;> simp_all

/-! ### Step 4: Generator certificate for 𝔭₂^10 -/

/-- Norm-form certificate: (-28)² + (-28)·3 + 36·3² = 1024 = 2^10.
    Generator of the principal ideal 𝔭₂^10 in 𝓞 K. -/
lemma norm_form_gen_1024_BSD : (-28 : ℤ) ^ 2 + (-28) * 3 + 36 * 3 ^ 2 = 1024 := by norm_num

/-! ### Step 5: Prime splitting in 𝓞 K -/

/-- p = 2 splits in K: X² − X + 36 ≡ 0 (mod 2) has solution X ≡ 0. -/
lemma prime_2_splits_BSD : ∃ x : ZMod 2, x ^ 2 - x + 36 = 0 := by decide

/-- p = 3 splits in K: X² − X + 36 ≡ 0 (mod 3) has solution X ≡ 0. -/
lemma prime_3_splits_BSD : ∃ x : ZMod 3, x ^ 2 - x + 36 = 0 := by decide

/-- p = 5 is inert in K: X² − X + 36 ≡ 0 (mod 5) has no solution. -/
lemma prime_5_inert_BSD : ∀ x : ZMod 5, x ^ 2 - x + 36 ≠ 0 := by decide

/-- p = 7 splits in K: X² − X + 36 ≡ 0 (mod 7) has solution X ≡ 3. -/
lemma prime_7_splits_BSD : ∃ x : ZMod 7, x ^ 2 - x + 36 = 0 := by decide

/-! ### Step 6: Class number open surfaces and combinator -/

/-- K1_ClassNumber_Upper_BSD: h(K) ≤ 10.
    STATUS: OPEN. Do NOT discharge with sorry/native_decide/trivial. -/
def K1_ClassNumber_Upper_BSD : Prop := NumberField.classNumber K ≤ 10

/-- K1_ClassNumber_Lower_BSD: 10 ≤ h(K).
    STATUS: OPEN. Do NOT discharge with sorry/native_decide/trivial. -/
def K1_ClassNumber_Lower_BSD : Prop := 10 ≤ NumberField.classNumber K

/-- K1_ClassNumber_Certificate_BSD: h(K) = 10.
    COMBINATOR (0 sorry, classical trio only): given the two open surfaces as
    explicit hypotheses, the equality is immediate. -/
theorem K1_ClassNumber_Certificate_BSD
    (h_upper : K1_ClassNumber_Upper_BSD)
    (h_lower : K1_ClassNumber_Lower_BSD) :
    NumberField.classNumber K = 10 :=
  Nat.le_antisymm h_upper h_lower

end Towers.BSD
