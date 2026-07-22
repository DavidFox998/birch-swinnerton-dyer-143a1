/-!
# BSD genesis-779: Closing BSD_aNBound_Finsupp_bridge_OPEN and BSD_tau_sqrt_OPEN

**Module**: `BSD/BSD_Genesis779_CLOSED.lean`
**Imports**: `Towers.BSD.BSD_Genesis778_CLOSED`
**sorry count**: 0
**axioms**: {propext, Classical.choice, Quot.sound}

## Proof chain this batch

Two avenues closed this batch:

  **Avenue 1 — Finsupp abs-product bridge (BSD_aNBound_Finsupp_bridge_OPEN)**:
    §1 finset_prod_int_cast          — (∏_ℤ f : ℤ) : ℝ = ∏_ℝ (f : ℝ)  (induction, proved)
    §2 BSD_aNBound_Finsupp_bridge_close — PROVED all n (n=0 by simp; n≥1 via §1)

  **Avenue 2 — τ(n)·√n product identity (BSD_tau_sqrt_OPEN)**:
    §3 finset_prod_nat_cast          — (∏_ℕ f : ℕ) : ℝ = ∏_ℝ (f : ℝ)  (induction, proved)
    §4 sqrt_pow_nat                  — √(x^n) = (√x)^n for x ≥ 0        (induction, proved)
    §5 sqrt_finset_prod              — √(∏ f_i) = ∏ √(f_i) for f_i ≥ 0  (induction, proved)
    §6 BSD_sqrt_factorization_close  — √n = ∏_p (√p)^{e_p} for n ≥ 1   (PROVED: §4+§5)
    §7 BSD_card_divisors_close       — τ(n) = ∏_p (e_p+1) for n ≥ 1    (PROVED: Nat.card_divisors)
    §8 BSD_tau_sqrt_close_pos        — BSD_tau_sqrt_OPEN n for n ≥ 1     (PROVED: §6+§7)
    §9 BSD_aNBound_all_n_v2         — ∀ n, BSD_aNBound_OPEN n           (PROVED: n=0 by simp)
   §10 BSD_LSeriesSummable_v2       — updated full conditional chain      (PROVED)

## Bug fix: BSD_tau_sqrt_OPEN 0 is false
  Finsupp.prod(empty) = 1 but sqrt(0)*0.divisors.card = 0.
  BSD_aNBound_all_n_v2 replaces BSD_aNBound_all_n with htau_pos (0<m only).
-/

import Towers.BSD.BSD_Genesis778_CLOSED
import Mathlib.NumberTheory.ArithmeticFunction

open BigOperators Real Nat ArithmeticFunction

namespace Towers.BSD

/-! ## §1. Cast of Finset.prod from ℤ to ℝ (induction — no Mathlib name required) -/

/-- Int.cast commutes with Finset.prod: proved by Finset induction over s. -/
private lemma finset_prod_int_cast {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ((∏ i ∈ s, f i : ℤ) : ℝ) = ∏ i ∈ s, (f i : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.cast_mul, ih]

/-! ## §2. BSD_aNBound_Finsupp_bridge_close (Avenue 1 CLOSED) -/

/-- **PROVED** (0 sorry): BSD_aNBound_Finsupp_bridge_OPEN n for every n ≥ 0.

  - n=0: a_n 0 = 0, Finsupp.prod over empty support = 1, so 0 ≤ 1 by norm_num.
  - n≥1: unfold a_n (n≠0 branch = Finsupp.prod in ℤ);
          cast to ℝ using finset_prod_int_cast;
          apply BSD_abs_prod_real; pointwise equality by split_ifs (|1|=1 for else branch). -/
theorem BSD_aNBound_Finsupp_bridge_close (n : ℕ) : BSD_aNBound_Finsupp_bridge_OPEN n := by
  simp only [BSD_aNBound_Finsupp_bridge_OPEN, Finsupp.prod]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: a_n 0 = 0, factorization.support = ∅, product = 1
    simp [a_n_zero, Nat.factorization_zero]
  · -- n ≥ 1
    have hn0 : n ≠ 0 := hn.ne'
    -- Cast (a_n n : ℝ) to the corresponding Finset.prod in ℝ
    have hcast : (a_n n : ℝ) =
        ∏ p ∈ n.factorization.support,
          if h : p.Prime then (haveI : Fact p.Prime := ⟨h⟩; (a_prime_pow p (n.factorization p) : ℝ))
          else 1 := by
      -- Unfold a_n: n≠0 branch is Finsupp.prod in ℤ
      have ha : a_n n = ∏ p ∈ n.factorization.support,
          if h : p.Prime then (haveI : Fact p.Prime := ⟨h⟩; a_prime_pow p (n.factorization p)) else 1 := by
        simp only [a_n, hn0, ↓reduceIte, Finsupp.prod]
      -- Cast ℤ-product to ℝ-product using finset_prod_int_cast
      calc (a_n n : ℝ)
          = ((∏ p ∈ n.factorization.support,
              if h : p.Prime then (haveI : Fact p.Prime := ⟨h⟩; a_prime_pow p (n.factorization p)) else 1 : ℤ) : ℝ) :=
            by exact_mod_cast ha
        _ = ∏ p ∈ n.factorization.support,
              ((if h : p.Prime then (haveI : Fact p.Prime := ⟨h⟩; a_prime_pow p (n.factorization p)) else 1 : ℤ) : ℝ) :=
            finset_prod_int_cast _ _
        _ = ∏ p ∈ n.factorization.support,
              if h : p.Prime then (haveI : Fact p.Prime := ⟨h⟩; (a_prime_pow p (n.factorization p) : ℝ)) else 1 := by
            congr 1; ext p; split_ifs with h
            · rfl
            · simp
    -- Apply BSD_abs_prod_real: |∏ f| = ∏ |f|
    rw [hcast, BSD_abs_prod_real]
    -- Both sides are pointwise equal: |if P then x else 1| = if P then |x| else 1
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro p _
    split_ifs with h
    · rfl
    · simp

/-! ## §3–5. Helper lemmas for Avenue 2 -/

/-- Nat.cast commutes with Finset.prod: proved by Finset induction. -/
private lemma finset_prod_nat_cast {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ((∏ i ∈ s, f i : ℕ) : ℝ) = ∏ i ∈ s, (f i : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, ih]

/-- √(x^n) = (√x)^n for x ≥ 0: proved by induction using Real.sqrt_mul. -/
private lemma sqrt_pow_nat (x : ℝ) (hx : 0 ≤ x) : ∀ n : ℕ, Real.sqrt (x ^ n) = Real.sqrt x ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), sqrt_pow_nat x hx n, pow_succ]

/-- √(∏ f_i) = ∏ √(f_i) for all f_i ≥ 0: proved by Finset induction using Real.sqrt_mul. -/
private lemma sqrt_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Real.sqrt_mul (hf _ (Finset.mem_insert_self _ _)),
        ih (fun i hi => hf i (Finset.mem_insert.mpr (Or.inr hi)))]

/-! ## §6. BSD_sqrt_factorization_close -/

/-- **PROVED** (0 sorry): ∏_p (√p)^{e_p} = √n for n ≥ 1.

  Chain:
  (a) Nat.factorization_prod_pow_eq_self: ∏_p p^{e_p} = n  (in ℕ)
  (b) finset_prod_nat_cast: cast to (n : ℝ) = ∏_p (p : ℝ)^{e_p}
  (c) sqrt_finset_prod: √(∏_p p^{e_p}) = ∏_p √(p^{e_p})
  (d) sqrt_pow_nat: √(p^{e_p}) = (√p)^{e_p} for p ≥ 0 -/
theorem BSD_sqrt_factorization_close (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ n.factorization.support, Real.sqrt (p : ℝ) ^ n.factorization p =
    Real.sqrt (n : ℝ) := by
  have hn0 : n ≠ 0 := hn.ne'
  -- (a+b): cast n to ℝ as the product of prime powers
  have hn_real : (n : ℝ) = ∏ p ∈ n.factorization.support, (p : ℝ) ^ n.factorization p := by
    have hfact := Nat.factorization_prod_pow_eq_self hn0
    simp only [Finsupp.prod] at hfact
    exact_mod_cast hfact.symm
  -- (c): sqrt distributes over the product
  rw [hn_real, sqrt_finset_prod _ _ (fun p _ => by positivity)]
  -- (d): (√p)^{e_p} = √(p^{e_p}), i.e. reverse sqrt_pow_nat
  congr 1; ext p
  exact (sqrt_pow_nat (p : ℝ) (by positivity) (n.factorization p)).symm

/-! ## §7. BSD_card_divisors_close -/

/-- **PROVED** (0 sorry): τ(n) = ∏_p (e_p + 1) for n ≥ 1, as real numbers.

  Uses Nat.card_divisors (proved in Mathlib.NumberTheory.ArithmeticFunction, line 1291):
    n.divisors.card = n.primeFactors.prod (n.factorization · + 1)
  where n.primeFactors = n.factorization.support definitionally. -/
theorem BSD_card_divisors_close (n : ℕ) (hn : 0 < n) :
    (n.divisors.card : ℝ) =
    ∏ p ∈ n.factorization.support, (n.factorization p + 1 : ℝ) := by
  have hcard := Nat.card_divisors hn.ne'
  -- hcard : n.divisors.card = n.primeFactors.prod (n.factorization · + 1)
  -- n.primeFactors = n.factorization.support definitionally
  have hcard' : n.divisors.card =
      ∏ p ∈ n.factorization.support, (n.factorization p + 1) := by
    convert hcard using 2
    simp [Nat.primeFactors]
  rw [hcard', finset_prod_nat_cast]
  push_cast; rfl

/-! ## §8. BSD_tau_sqrt_close_pos (Avenue 2 CLOSED for n ≥ 1) -/

/-- **PROVED** (0 sorry): BSD_tau_sqrt_OPEN n for every n ≥ 1.

  Proof:
  (1) On n.factorization.support all entries are prime (Nat.prime_of_mem_primeFactors);
      eliminate the dif guard — all entries evaluate to the true branch.
  (2) Split ∏[(e+1)(√p)^e] = [∏(e+1)] * [∏(√p)^e]  via Finset.prod_mul_distrib.
  (3) [∏(e+1)] = τ(n) via BSD_card_divisors_close (§7, reversed).
  (4) [∏(√p)^e] = √n via BSD_sqrt_factorization_close (§6).
  (5) τ(n) * √n = √n * τ(n) by ring. -/
theorem BSD_tau_sqrt_close_pos (n : ℕ) (hn : 0 < n) : BSD_tau_sqrt_OPEN n := by
  simp only [BSD_tau_sqrt_OPEN, Finsupp.prod]
  have hn0 : n ≠ 0 := hn.ne'
  -- (1) All p in n.factorization.support are prime
  have hprime : ∀ p ∈ n.factorization.support, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  -- Eliminate the dif guard: on support, condition is always true
  have hsimp : ∏ p ∈ n.factorization.support,
      (if h : p.Prime then (n.factorization p + 1 : ℝ) * Real.sqrt (p : ℝ) ^ n.factorization p
       else 1) =
      ∏ p ∈ n.factorization.support,
        (n.factorization p + 1 : ℝ) * Real.sqrt (p : ℝ) ^ n.factorization p :=
    Finset.prod_congr rfl (fun p hp => dif_pos (hprime p hp))
  rw [hsimp]
  -- (2) Split the product: ∏(f*g) = (∏f) * (∏g)
  rw [Finset.prod_mul_distrib]
  -- (3) ∏(e+1) = τ(n): use BSD_card_divisors_close (reversed)
  rw [← BSD_card_divisors_close n hn]
  -- (4) ∏(√p)^e = √n: use BSD_sqrt_factorization_close
  rw [BSD_sqrt_factorization_close n hn]
  -- (5) τ(n) * √n = √n * τ(n)
  ring

/-! ## §9. BSD_aNBound_all_n_v2 -/

/-- **PROVED** (0 sorry): ∀ n, BSD_aNBound_OPEN n.

  Replaces BSD_aNBound_all_n from genesis-778.

  Bug in BSD_aNBound_all_n: its hypothesis `htau : ∀ m, BSD_tau_sqrt_OPEN m` requires
  BSD_tau_sqrt_OPEN 0 = (Finsupp.prod ∅ f = √0 · |∅|) = (1 = 0 · 0) = (1 = 0), which is FALSE.
  BSD_aNBound_all_n cannot be instantiated from consistent axioms.

  Fix: htau_pos only requires 0 < m; n=0 is handled directly:
    BSD_aNBound_OPEN 0 = |a_n 0| ≤ √0 · 0.divisors.card = |0| ≤ 0 = 0 ≤ 0. -/
theorem BSD_aNBound_all_n_v2
    (hGate1  : ∀ (q : ℕ) (hq : Fact q.Prime) (j : ℕ), BSD_PrimePowBound_OPEN q j)
    (hbridge : ∀ m : ℕ, BSD_aNBound_Finsupp_bridge_OPEN m)
    (hprod   : ∀ m : ℕ, BSD_Finsupp_prod_le_OPEN m)
    (htau_pos : ∀ m : ℕ, 0 < m → BSD_tau_sqrt_OPEN m) :
    ∀ n : ℕ, BSD_aNBound_OPEN n := by
  intro n
  simp only [BSD_aNBound_OPEN]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: |a_n 0| = 0 = √0 · 0.divisors.card = 0 · 0 = 0
    simp [a_n_zero, Nat.divisors_zero]
  · -- n ≥ 1: walk the calc chain
    calc |(a_n n : ℝ)|
        ≤ n.factorization.prod (fun p e =>
            if h : p.Prime then haveI : Fact p.Prime := ⟨h⟩; |(a_prime_pow p e : ℝ)| else 1) :=
            hbridge n
      _ ≤ n.factorization.prod (fun p e =>
            if h : p.Prime then (e + 1 : ℝ) * Real.sqrt (p : ℝ) ^ e else 1) :=
            hprod n hGate1
      _ = Real.sqrt (n : ℝ) * n.divisors.card :=
            htau_pos n hn

/-! ## §10. BSD_LSeriesSummable_v2 -/

/-- **PROVED** (0 sorry): updated BSD_LSeriesSummable_OPEN conditional chain.

  Same structure as BSD_LSeriesSummable_conditional from genesis-778, but uses
  BSD_aNBound_all_n_v2 (corrected htau_pos hypothesis: ∀ m, 0 < m → BSD_tau_sqrt_OPEN m). -/
theorem BSD_LSeriesSummable_v2
    (hGate1   : ∀ (q : ℕ) (hq : Fact q.Prime) (j : ℕ), BSD_PrimePowBound_OPEN q j)
    (hbridge  : ∀ m : ℕ, BSD_aNBound_Finsupp_bridge_OPEN m)
    (hprod    : ∀ m : ℕ, BSD_Finsupp_prod_le_OPEN m)
    (htau_pos : ∀ m : ℕ, 0 < m → BSD_tau_sqrt_OPEN m)
    (htau_bd  : BSD_TauBound_OPEN)
    (h_bigO   : BSD_isBigO_to_LSeries_OPEN) :
    BSD_LSeriesSummable_OPEN :=
  h_bigO (fun ε hε => BSD_aNBound_times_tau_isBigO
    (BSD_aNBound_all_n_v2 hGate1 hbridge hprod htau_pos) htau_bd ε hε)

/-! ## Summary -/

/-!
### Genesis-779: Avenues 1 and 2 CLOSED

**Avenue 1 — BSD_aNBound_Finsupp_bridge_OPEN**: CLOSED (0 sorry, all n, unconditional)
  `BSD_aNBound_Finsupp_bridge_close : ∀ n, BSD_aNBound_Finsupp_bridge_OPEN n`
  Key: finset_prod_int_cast (§1, induction) + BSD_abs_prod_real (genesis-778 §1)

**Avenue 2 — BSD_tau_sqrt_OPEN**: CLOSED for n ≥ 1 (0 sorry, unconditional)
  `BSD_tau_sqrt_close_pos : ∀ n, 0 < n → BSD_tau_sqrt_OPEN n`
  Key: Nat.card_divisors + Nat.factorization_prod_pow_eq_self + sqrt_finset_prod (induction)

**Bug fix: BSD_tau_sqrt_OPEN 0 is false**
  0.factorization.prod f = 1 (empty product) ≠ √0 · 0.divisors.card = 0 · 0 = 0.
  BSD_aNBound_all_n required BSD_tau_sqrt_OPEN 0, making it unprovable from True axioms.
  BSD_aNBound_all_n_v2 fixes this via rcases (n=0 by simp; n≥1 via htau_pos).

**Helper lemmas proved (all by Finset induction — no exotic API):**
  finset_prod_int_cast  — (∏_ℤ f) : ℝ = ∏_ℝ (f : ℝ)
  finset_prod_nat_cast  — (∏_ℕ f) : ℝ = ∏_ℝ (f : ℝ)
  sqrt_pow_nat          — √(x^n) = (√x)^n for x ≥ 0
  sqrt_finset_prod      — √(∏ f) = ∏ √f for all f_i ≥ 0

**Mathlib APIs used (confirmed in v4.12.0):**
  Nat.card_divisors (ArithmeticFunction.lean L1291) — τ(n) = n.primeFactors.prod (e+1)
  Nat.factorization_prod_pow_eq_self               — ∏ p^e_p = n
  Nat.prime_of_mem_primeFactors                    — support entries are prime
  Nat.support_factorization                        — primeFactors = factorization.support
  Real.sqrt_mul                                    — √(xy) = √x · √y for x ≥ 0
  Finset.prod_mul_distrib                          — ∏(f·g) = (∏f) · (∏g)

Clay gate count: 2 (unchanged). BSD: OPEN. No Clay claim. 0 sorry. Classical trio only.
-/

end Towers.BSD
