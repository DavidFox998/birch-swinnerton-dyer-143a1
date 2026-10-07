/-
  Partial Group D, continued. Prime powers on the 84 checked primes.

  Where `|a_p| ≤ 2√p`, the Hecke sequence matches the Chebyshev polynomial
  of the second kind: `a_{p^k} = U_k(a_p / (2√p)) · (√p)^k`.
  For `|x| ≤ 1`, `|U_k(x)| ≤ k + 1`, by the sine bound
  `|sin((k+1)θ)| ≤ (k+1)|sin θ|` and the endpoint values `U_k(±1)`.
  The triangle inequality on the recurrence does not give this coefficient.

  The hypothesis `|a_p| ≤ 2√p` is the compiled check on the 84 primes.
  It is not known for every prime. For `n ≥ 1` whose prime factors all lie
  in that set, multiplicativity gives `|a_n| ≤ τ(n) √n`, and the divisor
  bound upgrades this to `|a_n| ≤ D n^{1/2+ε}`.
  `BSD_LSeriesSummable_OPEN` quantifies over every positive integer and
  stays NEEDS_AUTHORING. The 9 assessed definitions were not rewritten.
  No new point count. No sorry.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Towers.BSD.BSD_TauBound_Clean

open Polynomial Real

namespace Towers.BSD

private lemma abs_sin_mul_le (n : ℕ) (θ : ℝ) :
    |sin ((n + 1) * θ)| ≤ (n + 1 : ℝ) * |sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
    simp_rw [hc] at ih ⊢
    have harg : ((n : ℝ) + 1 + 1) * θ = ((n : ℝ) + 1) * θ + θ := by ring
    rw [harg, sin_add]
    have hcos1 : |cos θ| ≤ 1 := abs_cos_le_one θ
    have hcos2 : |cos (((n : ℝ) + 1) * θ)| ≤ 1 := abs_cos_le_one _
    have h1 : |sin (((n : ℝ) + 1) * θ) * cos θ| ≤ |sin (((n : ℝ) + 1) * θ)| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hcos1
    have h2 : |cos (((n : ℝ) + 1) * θ) * sin θ| ≤ |sin θ| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hcos2
    calc |sin (((n : ℝ) + 1) * θ) * cos θ + cos (((n : ℝ) + 1) * θ) * sin θ|
        ≤ |sin (((n : ℝ) + 1) * θ) * cos θ| + |cos (((n : ℝ) + 1) * θ) * sin θ| :=
          abs_add _ _
      _ ≤ |sin (((n : ℝ) + 1) * θ)| + |sin θ| := by linarith
      _ ≤ ((n : ℝ) + 1) * |sin θ| + |sin θ| := by linarith [ih]
      _ = ((n : ℝ) + 1 + 1) * |sin θ| := by ring

private lemma chebyshev_U_eval_one (n : ℕ) :
    (Chebyshev.U ℝ (n : ℤ)).eval (1 : ℝ) = (n : ℝ) + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [Chebyshev.U_zero]
    | succ n =>
      cases n with
      | zero =>
        simp [Chebyshev.U_one, eval_mul, eval_ofNat, eval_X]
        norm_num
      | succ n =>
        rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by simp, Chebyshev.U_add_two]
        simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
        rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp]
        rw [ih (n + 1) (by omega), ih n (by omega)]
        push_cast
        ring

private lemma chebyshev_U_eval_neg_one (n : ℕ) :
    (Chebyshev.U ℝ (n : ℤ)).eval (-1 : ℝ) = (-1 : ℝ) ^ n * ((n : ℝ) + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [Chebyshev.U_zero]
    | succ n =>
      cases n with
      | zero =>
        simp [Chebyshev.U_one, eval_mul, eval_ofNat, eval_X]
        norm_num
      | succ n =>
        rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by simp, Chebyshev.U_add_two]
        simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
        rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp]
        rw [ih (n + 1) (by omega), ih n (by omega)]
        push_cast
        ring_nf

private lemma abs_chebyshev_U_le (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(Chebyshev.U ℝ (n : ℤ)).eval x| ≤ (n : ℝ) + 1 := by
  by_cases hx1 : x = 1
  · rw [hx1, chebyshev_U_eval_one]
    exact le_of_eq (abs_of_nonneg (by positivity))
  · by_cases hxm : x = -1
    · rw [hxm, chebyshev_U_eval_neg_one, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact le_of_eq (abs_of_nonneg (by positivity))
    · let θ : ℝ := arccos x
      have hxlo : -1 ≤ x := (abs_le.mp hx).1
      have hxhi : x ≤ 1 := (abs_le.mp hx).2
      have hcos : cos θ = x := cos_arccos hxlo hxhi
      have hsin_nonneg : 0 ≤ sin θ :=
        sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg x) (arccos_le_pi x)
      have hsin_pos : 0 < sin θ := by
        rw [sin_arccos]
        refine sqrt_pos.mpr ?_
        have hsq : x ^ 2 < 1 := by
          have hle : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, hx]
          by_contra hge
          push_neg at hge
          have heq : x ^ 2 = 1 := le_antisymm hle hge
          have : x = 1 ∨ x = -1 := by
            have hfac : (x - 1) * (x + 1) = 0 := by linear_combination heq
            rcases mul_eq_zero.mp hfac with h | h
            · exact Or.inl (sub_eq_zero.mp h)
            · exact Or.inr (eq_neg_of_add_eq_zero_left h)
          cases this with
          | inl h => exact hx1 h
          | inr h => exact hxm h
        linarith
      have hU := Chebyshev.U_real_cos θ (n : ℤ)
      rw [hcos] at hU
      have hidx : ((n : ℤ) + 1) * θ = ((n + 1 : ℕ) : ℝ) * θ := by
        push_cast
        ring_nf
      have habs : |(Chebyshev.U ℝ (n : ℤ)).eval x| * sin θ =
          |sin (((n + 1 : ℕ) : ℝ) * θ)| := by
        have hmul : |(Chebyshev.U ℝ (n : ℤ)).eval x| * sin θ =
            |((Chebyshev.U ℝ (n : ℤ)).eval x) * sin θ| := by
          rw [abs_mul, abs_of_nonneg hsin_nonneg]
        rw [hmul, hU, hidx]
      have hsin_le : |sin (((n + 1 : ℕ) : ℝ) * θ)| ≤ ((n : ℝ) + 1) * sin θ := by
        simpa [abs_of_nonneg hsin_nonneg] using abs_sin_mul_le n θ
      have hle : |(Chebyshev.U ℝ (n : ℤ)).eval x| * sin θ ≤
          ((n : ℝ) + 1) * sin θ := by
        rw [habs]
        exact hsin_le
      exact le_of_mul_le_mul_right hle hsin_pos

private lemma a_prime_pow_as_chebyshev
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (a_prime_pow p k : ℝ) =
      (Chebyshev.U ℝ (k : ℤ)).eval ((a_p p : ℝ) / (2 * sqrt (p : ℝ))) *
        sqrt (p : ℝ) ^ k := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (‹Fact p.Prime›.out).pos
  have hs_pos : 0 < sqrt (p : ℝ) := sqrt_pos.mpr hp_pos
  have hs_sq : sqrt (p : ℝ) ^ 2 = (p : ℝ) := sq_sqrt (le_of_lt hp_pos)
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simp [a_prime_pow, Chebyshev.U_zero]
    | succ k =>
      cases k with
      | zero =>
        simp only [a_prime_pow, Chebyshev.U_one, eval_mul, eval_ofNat, eval_X, pow_one]
        field_simp [hs_pos.ne']
        ring
      | succ k =>
        have ih1 := ih (k + 1) (by omega)
        have ih0 := ih k (by omega)
        rw [show a_prime_pow p (k + 2) =
            a_p p * a_prime_pow p (k + 1) - (p : ℤ) * a_prime_pow p k from rfl]
        rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_natCast, ih1, ih0]
        rw [show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by simp, Chebyshev.U_add_two]
        simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
        rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by simp]
        -- Name the square root so `p = s^2` cannot rewrite inside `√p`.
        generalize hsdef : sqrt (p : ℝ) = s
        have hs_pos' : (0 : ℝ) < s := by rw [← hsdef]; exact hs_pos
        have hs_sq' : s ^ 2 = (p : ℝ) := by rw [← hsdef]; exact hs_sq
        field_simp [hs_pos'.ne']
        simp only [pow_add, pow_one]
        rw [← hs_sq']
        ring

/-- For each of the 84 checked primes and every `k`, `|a_{p^k}| ≤ (k+1) p^{k/2}`.
    Uses `|a_p| ≤ 2√p` from the compiled degree form. Not every prime.
    Not `BSD_LSeriesSummable_OPEN`. -/
theorem BSD_prime_pow_bound_checked
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) (k : ℕ) :
    |(a_prime_pow p k : ℝ)| ≤ (k + 1 : ℝ) * sqrt (p : ℝ) ^ k := by
  have habs : |(a_p p : ℝ)| ≤ 2 * sqrt (p : ℝ) :=
    (BSD_Hasse_Forms_Equiv_84 p hp).1
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (‹Fact p.Prime›.out).pos
  have hs_pos : 0 < sqrt (p : ℝ) := sqrt_pos.mpr hp_pos
  have hx : |(a_p p : ℝ) / (2 * sqrt (p : ℝ))| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
      abs_of_pos hs_pos]
    rw [div_le_one (by positivity)]
    exact habs
  rw [a_prime_pow_as_chebyshev p k, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hs_pos) k)]
  exact mul_le_mul_of_nonneg_right (abs_chebyshev_U_le k hx) (pow_nonneg (le_of_lt hs_pos) k)

private theorem finset_prod_cast {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (↑(∏ i in s, f i) : ℝ) = ∏ i in s, (f i : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, ih]

private theorem finset_prod_rpow {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    (∏ i in s, f i) ^ r = ∏ i in s, (f i) ^ r := by
  induction s using Finset.induction_on with
  | empty => simp [Real.one_rpow]
  | insert ha ih =>
    rename_i _inst a s'
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    rw [Real.mul_rpow (hf a (Finset.mem_insert_self a s'))
      (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi)))]
    rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma a_n_factor_prod (n : ℕ) (hn : 0 < n) :
    a_n n = ∏ p in n.factorization.support,
      if h : p.Prime then
        haveI : Fact p.Prime := ⟨h⟩
        a_prime_pow p (n.factorization p)
      else 1 := by
  rw [a_n, if_neg hn.ne', Finsupp.prod]

/-- `n ≥ 1` with every prime factor among the 84 checked primes.
    `|a_n| ≤ τ(n) √n ≤ D n^{1/2+ε}`. Higher prime powers are included.
    A prime outside the 84 is not covered. `BSD_LSeriesSummable_OPEN`
    quantifies over every positive integer and is not proved. -/
theorem BSD_an_checked_support_bound
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 0 < n)
    (hfac : ∀ p : ℕ, p ∈ n.primeFactors → p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    ∃ D : ℝ, 0 < D ∧ |(a_n n : ℝ)| ≤ D * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨D, hD, hτ⟩ := BSD_tau_bound_of_divisors ε hε
  have hn0 : n ≠ 0 := hn.ne'
  set S := n.factorization.support with hS
  let f : ℕ → ℤ := fun p =>
    if h : p.Prime then
      haveI : Fact p.Prime := ⟨h⟩
      a_prime_pow p (n.factorization p)
    else 1
  have h_an : a_n n = ∏ p in S, f p := by
    simpa [f, hS] using a_n_factor_prod n hn
  have hpoint : ∀ p ∈ S, (Int.cast (R := ℝ) |f p|) ≤
      ((n.factorization p : ℝ) + 1) * sqrt (p : ℝ) ^ n.factorization p := by
    intro p hp
    have hp_pf : p ∈ n.primeFactors :=
      (Nat.support_factorization n) ▸ (hS.symm ▸ hp)
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
    haveI : Fact p.Prime := ⟨hp_prime⟩
    have hf : f p = a_prime_pow p (n.factorization p) := by simp [f, hp_prime]
    rw [Int.cast_abs, hf]
    exact BSD_prime_pow_bound_checked p (hfac p hp_pf) (n.factorization p)
  have habs : |(a_n n : ℝ)| ≤ (n.divisors.card : ℝ) * sqrt (n : ℝ) := by
    have habsZ : |∏ p in S, f p| = ∏ p in S, |f p| := Finset.abs_prod _ _
    have hcast_abs : (Int.cast (R := ℝ) |a_n n|) = |(a_n n : ℝ)| := Int.cast_abs
    have hcast_prod :
        Int.cast (R := ℝ) (∏ p in S, |f p|) =
          ∏ p in S, Int.cast (R := ℝ) |f p| :=
      map_prod (Int.castRingHom ℝ) (fun p => |f p|) S
    have hprod_le :
        ∏ p in S, Int.cast (R := ℝ) |f p| ≤
          ∏ p in S, (((n.factorization p : ℝ) + 1) *
            sqrt (p : ℝ) ^ n.factorization p) :=
      Finset.prod_le_prod (fun _ _ => by positivity) hpoint
    have hsplit :
        ∏ p in S, (((n.factorization p : ℝ) + 1) *
            sqrt (p : ℝ) ^ n.factorization p) =
          (∏ p in S, ((n.factorization p : ℝ) + 1)) *
            ∏ p in S, sqrt (p : ℝ) ^ n.factorization p :=
      Finset.prod_mul_distrib
    have htau : ∏ p in S, ((n.factorization p : ℝ) + 1) =
        (n.divisors.card : ℝ) := by
      rw [divisors_card_factorization n hn, ← hS]
    have hsqrt_prod : ∏ p in S, sqrt (p : ℝ) ^ n.factorization p = sqrt (n : ℝ) := by
      have hnat : ∏ p in S, p ^ n.factorization p = n := by
        have h := Nat.factorization_prod_pow_eq_self hn0
        simp only [Finsupp.prod] at h
        simpa [hS] using h
      have hcast : (n : ℝ) = ∏ p in S, (p : ℝ) ^ n.factorization p := by
        have h : (n : ℝ) = ↑(∏ p in S, p ^ n.factorization p) := by
          exact_mod_cast hnat.symm
        rw [h, finset_prod_cast]
        congr 1
        ext p
        push_cast
        rfl
      have hterm : ∀ p ∈ S, sqrt (p : ℝ) ^ n.factorization p =
          ((p : ℝ) ^ n.factorization p) ^ ((1 : ℝ) / 2) := by
        intro p _
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
        rw [← Real.rpow_mul (Nat.cast_nonneg p)]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
        congr 1
        ring
      have hrewrite : ∏ p in S, sqrt (p : ℝ) ^ n.factorization p =
          ∏ p in S, ((p : ℝ) ^ n.factorization p) ^ ((1 : ℝ) / 2) :=
        Finset.prod_congr rfl hterm
      rw [hrewrite]
      rw [← finset_prod_rpow S (fun p => (p : ℝ) ^ n.factorization p)
        (fun p _ => pow_nonneg (Nat.cast_nonneg p) _) ((1 : ℝ) / 2), ← hcast]
      exact (Real.sqrt_eq_rpow (n : ℝ)).symm
    calc |(a_n n : ℝ)|
        = Int.cast (R := ℝ) |a_n n| := hcast_abs.symm
      _ = Int.cast (R := ℝ) |∏ p in S, f p| := by rw [h_an]
      _ = Int.cast (R := ℝ) (∏ p in S, |f p|) := by rw [habsZ]
      _ = ∏ p in S, Int.cast (R := ℝ) |f p| := hcast_prod
      _ ≤ ∏ p in S, (((n.factorization p : ℝ) + 1) *
          sqrt (p : ℝ) ^ n.factorization p) := hprod_le
      _ = (n.divisors.card : ℝ) * sqrt (n : ℝ) := by rw [hsplit, htau, hsqrt_prod]
  have hmul : (n.divisors.card : ℝ) * sqrt (n : ℝ) ≤
      D * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
    have hpow : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ε =
        (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
      rw [← Real.rpow_add (by exact_mod_cast hn) ((1 : ℝ) / 2) ε]
    have hsqrt_eq : sqrt (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.sqrt_eq_rpow (n : ℝ)
    calc (n.divisors.card : ℝ) * sqrt (n : ℝ)
        = (n.divisors.card : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := by rw [hsqrt_eq]
      _ ≤ (D * (n : ℝ) ^ ε) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_right (hτ n hn)
          exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      _ = D * ((n : ℝ) ^ ε * (n : ℝ) ^ ((1 : ℝ) / 2)) := by ring
      _ = D * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
          rw [mul_comm ((n : ℝ) ^ ε), hpow]
  refine ⟨D, hD, habs.trans hmul⟩

/-- The prime-power bound on the checked set does not prove summability of
    the L-series. The registry summability name stays `True`. The root
    statement `BSD_LSeriesSummable_OPEN` is not discharged. `84 ≠ 54`. -/
theorem BSD_prime_pow_not_Lseries :
    BSD_MissingDefinitionsRegistry.BSD_EulerConvergence_OPEN = True ∧
      BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      (84 : ℕ) ≠ 54 :=
  ⟨rfl, BSD_Finite_Hasse_CheckedPrimes_card, BSD_54_of_504.2.2⟩

end Towers.BSD
