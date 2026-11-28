import Towers.BSD.BSD_ClassNumber

/-
  # BSD_NormFormBounds — Tier 2 Track A: norm-form lower bound for 𝓞_K = ℤ[ω]

  Clean Tier 2 entry point.  The field K = ℚ(√-143) has ring of integers
  𝓞_K = ℤ[ω], ω = (1+√-143)/2, ω² = ω − 36.

  Every element of 𝓞_K has the form a + bω (a, b : ℤ).
  The algebraic norm is the quadratic form

      N(a + bω) = a² + ab + 36b²  (the Euler/Gauss form of discriminant -143).

  KEY IDENTITY (proved):
      4 · N(a + bω) = (2a + b)² + 143 · b²                     [normForm_four_eq]

  LOWER BOUND (proved):
      b ≠ 0  →  N(a + bω) ≥ 36                                 [normForm_lower_bound]

  MINKOWSKI-RELEVANT IMPOSSIBILITIES (all proved, sorry = 0):
      ¬ ∃ a b : ℤ, N(a + bω) = 2    [normForm_two_impossible]
      ¬ ∃ a b : ℤ, N(a + bω) = 3    [normForm_three_impossible]
      ¬ ∃ a b : ℤ, N(a + bω) = 5    [normForm_five_impossible]
      ¬ ∃ a b : ℤ, N(a + bω) = 7    [normForm_seven_impossible]

  MINKOWSKI BOUND (proved in BSD_NumberField):
      (2/π)·√143 < 8  [minkowski_lt_eight_BSD]
  →  every ideal class has a representative ideal of norm ≤ 7.
  →  the only norms ≤ 7 that CAN be hit are N = 1 and N = 4 (= 4·1²).
  →  at most the primes dividing N = 4 (i.e., only p = 2) contribute
     non-principal ideal classes.

  NAMED OPEN SURFACES:
      BSD_ClassNumber_Upper_OPEN : h(K) ≤ 10
      BSD_ClassNumber_Lower_OPEN : 10 ≤ h(K)

  COMBINATOR (0 sorry):
      BSD_ClassNumber_eq_ten_cond : h(K) = 10  (conditional)

  SORRY: 0 in proved results.  Classical trio axiom footprint.
-/

namespace Towers.BSD

open NumberField

/-! ### Norm form definition -/

/-- N(a + bω) = a² + ab + 36b² — the norm form of 𝓞_K = ℤ[ω] in the {1, ω} basis.
    Discriminant: disc(normForm) = 1² − 4·36 = −143. -/
def normForm (a b : ℤ) : ℤ := a ^ 2 + a * b + 36 * b ^ 2

/-- KEY IDENTITY: 4 · normForm(a, b) = (2a+b)² + 143b².
    This identity — the "completing the square" step — is the engine
    for all lower-bound and impossibility proofs below. -/
lemma normForm_four_eq (a b : ℤ) :
    4 * normForm a b = (2 * a + b) ^ 2 + 143 * b ^ 2 := by
  unfold normForm; ring

/-! ### Lower bound -/

lemma one_le_sq_of_ne_zero {n : ℤ} (hn : n ≠ 0) : 1 ≤ n ^ 2 := by
  rcases lt_or_gt_of_ne hn with h | h
  · nlinarith [sq_nonneg (n + 1)]
  · nlinarith [sq_nonneg (n - 1)]

/-- If b ≠ 0 then N(a + bω) ≥ 36.
    Proof: 4·N = (2a+b)² + 143b² ≥ 143b² ≥ 143 > 143 when b² ≥ 1.
    So 4·N ≥ 143, and N ∈ ℤ forces N ≥ ⌈143/4⌉ = 36. -/
lemma normForm_lower_bound {a b : ℤ} (hb : b ≠ 0) : 36 ≤ normForm a b := by
  have hb2 : 1 ≤ b ^ 2 := one_le_sq_of_ne_zero hb
  nlinarith [normForm_four_eq a b, sq_nonneg (2 * a + b)]

/-! ### Minkowski-relevant impossibilities -/

/-- N(a + bω) = 2 has no integer solution.
    Proof: b = 0 forces a² = 2 (impossible); b ≠ 0 gives N ≥ 36 > 2. -/
theorem normForm_two_impossible : ¬ ∃ a b : ℤ, normForm a b = 2 := by
  rintro ⟨a, b, h⟩
  by_cases hb : b = 0
  · simp only [normForm, hb, mul_zero, add_zero, zero_mul] at h
    have ha_le : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
    have ha_ge : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
    interval_cases a <;> simp_all [normForm]
  · linarith [normForm_lower_bound (a := a) hb, h.symm.le]

/-- N(a + bω) = 3 has no integer solution. -/
theorem normForm_three_impossible : ¬ ∃ a b : ℤ, normForm a b = 3 := by
  rintro ⟨a, b, h⟩
  by_cases hb : b = 0
  · simp only [normForm, hb, mul_zero, add_zero, zero_mul] at h
    have ha_le : a ≤ 1 := by nlinarith [sq_nonneg (a - 2)]
    have ha_ge : -1 ≤ a := by nlinarith [sq_nonneg (a + 2)]
    interval_cases a <;> simp_all [normForm]
  · linarith [normForm_lower_bound (a := a) hb, h.symm.le]

/-- N(a + bω) = 5 has no integer solution. -/
theorem normForm_five_impossible : ¬ ∃ a b : ℤ, normForm a b = 5 := by
  rintro ⟨a, b, h⟩
  by_cases hb : b = 0
  · simp only [normForm, hb, mul_zero, add_zero, zero_mul] at h
    have ha_le : a ≤ 2 := by nlinarith [sq_nonneg (a - 3)]
    have ha_ge : -2 ≤ a := by nlinarith [sq_nonneg (a + 3)]
    interval_cases a <;> simp_all [normForm]
  · linarith [normForm_lower_bound (a := a) hb, h.symm.le]

/-- N(a + bω) = 7 has no integer solution. -/
theorem normForm_seven_impossible : ¬ ∃ a b : ℤ, normForm a b = 7 := by
  rintro ⟨a, b, h⟩
  by_cases hb : b = 0
  · simp only [normForm, hb, mul_zero, add_zero, zero_mul] at h
    have ha_le : a ≤ 2 := by nlinarith [sq_nonneg (a - 3)]
    have ha_ge : -2 ≤ a := by nlinarith [sq_nonneg (a + 3)]
    interval_cases a <;> simp_all [normForm]
  · linarith [normForm_lower_bound (a := a) hb, h.symm.le]

/-- All four Minkowski-relevant prime norms are impossible:
    the norm form a² + ab + 36b² represents none of {2, 3, 5, 7}. -/
theorem normForm_no_small_primes :
    (¬ ∃ a b : ℤ, normForm a b = 2) ∧
    (¬ ∃ a b : ℤ, normForm a b = 3) ∧
    (¬ ∃ a b : ℤ, normForm a b = 5) ∧
    (¬ ∃ a b : ℤ, normForm a b = 7) :=
  ⟨normForm_two_impossible, normForm_three_impossible,
   normForm_five_impossible, normForm_seven_impossible⟩

/-! ### Connection to BSD_ClassNumber -/

/-- normForm agrees with the explicit form used throughout BSD_ClassNumber. -/
lemma normForm_eq_bsd (a b : ℤ) :
    normForm a b = a ^ 2 + a * b + 36 * b ^ 2 := rfl

/-- BSD norm-form impossibilities recast in normForm language. -/
lemma normForm_two_impossible_direct (a b : ℤ) : normForm a b ≠ 2 :=
  norm_form_no_norm_two_BSD a b

lemma normForm_three_impossible_direct (a b : ℤ) : normForm a b ≠ 3 :=
  norm_form_no_norm_three_BSD a b

lemma normForm_five_impossible_direct (a b : ℤ) : normForm a b ≠ 5 :=
  norm_form_no_norm_five_BSD a b

lemma normForm_seven_impossible_direct (a b : ℤ) : normForm a b ≠ 7 :=
  norm_form_no_norm_seven_BSD a b

/-! ### Named open surfaces for the class number -/

/-- **BSD_ClassNumber_Upper_OPEN**: h(K) ≤ 10.

    Mathematical route (Minkowski):
    minkowski_lt_eight_BSD: (2/π)·√143 < 8 proves every ideal class has
    a representative of norm ≤ 7.  The four impossibilities above show
    that N = 2, 3, 5, 7 are not norms of elements of 𝓞_K, so those primes
    are either inert (contributing no class, prime_5_inert_BSD) or
    split into ideals whose classes are powers of the class [𝔭₂] or [𝔭₃] or [𝔭₇].
    Careful counting via prime splitting (prime_2/3/7_splits_BSD) gives ≤ 10
    classes total.

    Formal gap: the Minkowski bound applied to the class group of AdjoinRoot
    in Mathlib v4.12.0 needs ~80 lines of ClassGroup API work.
    STATUS: OPEN.  NOT discharged here. -/
def BSD_ClassNumber_Upper_OPEN : Prop := K1_ClassNumber_Upper_BSD

/-- **BSD_ClassNumber_Lower_OPEN**: 10 ≤ h(K).

    Mathematical route:
    norm_form_gen_1024_BSD shows (-28, 3) is the ℤ-coordinate pair with
    normForm(-28, 3) = 1024 = 2^10, proving 𝔭₂^10 is principal.
    The odd-power impossibilities (N=2,8,32,128,512 all impossible) prove
    𝔭₂^k non-principal for k = 1,…,9.  Hence ord([𝔭₂]) = 10 in h(K).

    Formal gap: ideal group API for AdjoinRoot in Mathlib v4.12.0.
    STATUS: OPEN.  NOT discharged here. -/
def BSD_ClassNumber_Lower_OPEN : Prop := K1_ClassNumber_Lower_BSD

/-! ### Combinator (0 sorry) -/

/-- h(K) = 10, given both OPEN surfaces as explicit hypotheses.
    COMBINATOR: 0 sorry, classical trio only.  NOT a brick. -/
theorem BSD_ClassNumber_eq_ten_cond
    (h_upper : BSD_ClassNumber_Upper_OPEN)
    (h_lower : BSD_ClassNumber_Lower_OPEN) :
    NumberField.classNumber K = 10 :=
  K1_ClassNumber_Certificate_BSD h_upper h_lower

/-! ### Tier 2A evidence summary -/

/-- All Tier 2A arithmetic evidence collected in one place. -/
theorem BSD_Tier2A_ArithEvidence :
    -- Key identity
    (∀ a b : ℤ, 4 * normForm a b = (2 * a + b) ^ 2 + 143 * b ^ 2) ∧
    -- Lower bound
    (∀ a b : ℤ, b ≠ 0 → 36 ≤ normForm a b) ∧
    -- Four impossibilities
    (¬ ∃ a b : ℤ, normForm a b = 2) ∧
    (¬ ∃ a b : ℤ, normForm a b = 3) ∧
    (¬ ∃ a b : ℤ, normForm a b = 5) ∧
    (¬ ∃ a b : ℤ, normForm a b = 7) ∧
    -- Generator certificate: normForm(-28, 3) = 1024 = 2^10
    (normForm (-28) 3 = 1024) :=
  ⟨normForm_four_eq,
   fun a b hb => normForm_lower_bound hb,
   normForm_two_impossible,
   normForm_three_impossible,
   normForm_five_impossible,
   normForm_seven_impossible,
   by norm_num [normForm]⟩

end Towers.BSD
