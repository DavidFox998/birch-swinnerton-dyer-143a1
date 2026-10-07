/-
  Divisor bound extracted from hasseprimset/BSD_TauBound_small_proved.lean.
  No import of Towers.BSD.BSD_Genesis781_CLOSED.
  τ(n) ≤ D·n^ε for every ε > 0. Not the full L-series.
  Squarefree n supported on the 84 checked primes satisfy
  |a_n| ≤ D·n^{1/2+ε}. Prime powers p^k with k ≥ 2 stay open:
  the bound |a_{p^k}| ≤ (k+1)·p^{k/2} is the unformalized step.
  No sorry. No new E143_Finset enumeration.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Towers.BSD.BSD_More_Theorems_From_54

set_option maxHeartbeats 800000

open BigOperators Real Nat

namespace Towers.BSD

/-! ## §1. succ_le_two_pow -/

private theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    calc n + 1 + 1 ≤ 2 * (n + 1) := by omega
      _ ≤ 2 * 2 ^ n := by linarith
      _ = 2 ^ (n + 1) := by ring

/-! ## §2. bernoulli_ineq -/

private theorem bernoulli_ineq (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    1 + (k : ℝ) * x ≤ (1 + x) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hpow_ge1 : (1 : ℝ) ≤ (1 + x) ^ n := by
      have h1 := pow_le_pow_left (by norm_num : (0 : ℝ) ≤ 1)
                                 (by linarith : (1 : ℝ) ≤ 1 + x) n
      simp only [one_pow] at h1; exact h1
    rw [pow_succ]
    have lhs_eq : 1 + (↑(n + 1) : ℝ) * x = (1 + ↑n * x) + x := by push_cast; ring
    have rhs_eq : (1 + x) ^ n * (1 + x) = (1 + x) ^ n + x * (1 + x) ^ n := by ring
    rw [lhs_eq, rhs_eq]
    linarith [mul_nonneg hx (show (0 : ℝ) ≤ (1 + x) ^ n - 1 by linarith)]

/-! ## §3. finset_prod_cast -/

private theorem finset_prod_cast {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (↑(∏ i in s, f i) : ℝ) = ∏ i in s, (f i : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, ih]

/-! ## §4. finset_prod_rpow -/

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

/-! ## §5. factorization_rpow_eq -/

private theorem factorization_rpow_eq (n : ℕ) (hn : 0 < n) (ε : ℝ) :
    ∏ p in n.factorization.support, (p : ℝ) ^ (ε * n.factorization p) = (n : ℝ) ^ ε := by
  -- Step 1: n.factorization.prod (·^·) = n  as ℕ (unfold Finsupp.prod)
  have hnat : ∏ p in n.factorization.support, p ^ n.factorization p = n := by
    have h := Nat.factorization_prod_pow_eq_self hn.ne'
    simp only [Finsupp.prod] at h; exact h
  -- Step 2: cast to ℝ
  have hcast : (n : ℝ) = ∏ p in n.factorization.support, (p : ℝ) ^ n.factorization p := by
    have h : (n : ℝ) = ↑(∏ p in n.factorization.support, p ^ n.factorization p) :=
      by exact_mod_cast hnat.symm
    rw [h, finset_prod_cast]
    congr 1; ext p; push_cast; rfl
  -- Step 3: (n:ℝ)^ε = (∏ p^e_p)^ε = ∏ (p^e_p)^ε = ∏ p^(ε*e_p)
  rw [hcast, finset_prod_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _)]
  congr 1; ext p
  rw [← Real.rpow_natCast (p : ℝ) (n.factorization p),
      ← Real.rpow_mul (Nat.cast_nonneg p)]
  congr 1; ring

/-! ## §6. succ_le_rpow_large — large prime case: p^ε ≥ 2 -/

private theorem succ_le_rpow_large (k : ℕ) (β : ℝ) (hβ : 2 ≤ β) :
    (k + 1 : ℝ) ≤ β ^ k := by
  have hk1 : (k + 1 : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast succ_le_two_pow k
  have h2β : (2 : ℝ) ^ k ≤ β ^ k := pow_le_pow_left (by norm_num) hβ k
  linarith

/-! ## §7. succ_le_rpow_small — small prime case: 1 < p^ε < 2 -/

private theorem succ_le_rpow_small (k : ℕ) (β : ℝ) (hβ : 1 < β) :
    (k + 1 : ℝ) ≤ β / (β - 1) * β ^ k := by
  have hβ1 : 0 < β - 1 := by linarith
  have hpow : β * β ^ k = β ^ (k + 1) := by rw [mul_comm, pow_succ]
  rw [div_mul_eq_mul_div, le_div_iff₀ hβ1, hpow]
  -- Goal: (↑k + 1) * (β - 1) ≤ β^(k+1)
  -- Bernoulli: β^(k+1) = (1+(β-1))^(k+1) ≥ 1 + (k+1)*(β-1) ≥ (k+1)*(β-1)
  have hbern := bernoulli_ineq (k + 1) (β - 1) hβ1.le
  have hβeq : 1 + (β - 1) = β := by ring
  rw [hβeq] at hbern
  push_cast at hbern ⊢
  linarith

/-! ## §8. BSD_TauBound_small_proved -/

/-- **PROVED** (0 sorry, unconditional): BSD_TauBound_small_OPEN.

    For any 0 < ε < 1/2: ∃ D_ε > 0, τ(n) ≤ D_ε · n^ε for all n ≥ 1.

    Proof sketch:
    • τ(n) = ∏_{p|n} (e_p+1)  (BSD_card_divisors_close, genesis-779)
    • Large primes (p^ε ≥ 2): e_p+1 ≤ 2^{e_p} ≤ (p^ε)^{e_p} = p^{ε·e_p}  (§6)
    • Small primes (p^ε < 2): e_p+1 ≤ p^ε/(p^ε-1) · p^{ε·e_p}  (§7, Bernoulli)
    • D_ε = ∏_{p prime, p < 2^{1/ε}+2} p^ε/(p^ε-1)  (finite product, all factors ≥ 1)
    • ∏_{p|n} p^{ε·e_p} = n^ε  (§5) -/
lemma divisors_card_factorization (n : ℕ) (hn : 0 < n) :
    (n.divisors.card : ℝ) =
      ∏ p in n.factorization.support, ((n.factorization p : ℝ) + 1) := by
  have hcard := Nat.card_divisors hn.ne'
  rw [← Nat.support_factorization] at hcard
  rw [hcard, finset_prod_cast]
  refine Finset.prod_congr rfl fun p _ => ?_
  push_cast
  rfl

/-- `τ(n) = n.divisors.card ≤ D · n^ε` for every `ε > 0` and every `n ≥ 1`.
    Copied from `hasseprimset/BSD_TauBound_small_proved.lean` §1–§8.
    `Nat.card_divisors` replaces `BSD_card_divisors_close`. That lemma lived in
    `Towers.BSD.BSD_Genesis781_CLOSED`, which is not imported.
    This is not summability of the L-series. The prime-power bound
    `|a_{p^k}| ≤ (k+1) p^{k/2}` stays unformalized, so the coefficient bound
    for every `n` stays NEEDS_AUTHORING. -/
theorem BSD_tau_bound_of_divisors (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ D * (n : ℝ) ^ ε := by
  -- Finite threshold: primes p with p^ε < 2 satisfy p < 2^{1/ε} < B
  let B : ℕ := Nat.ceil ((2 : ℝ) ^ (1 / ε)) + 2
  let small_ps := (Finset.range B).filter Nat.Prime
  -- D_ε: product of p^ε/(p^ε-1) over primes p < B
  let D := ∏ p in small_ps, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1)
  -- D > 0: each factor positive since p^ε > 1 > 0 for prime p ≥ 2 and ε > 0
  have hD_pos : 0 < D := by
    apply Finset.prod_pos
    intro p hp
    simp only [small_ps, Finset.mem_filter] at hp
    have hp_ge2 : 2 ≤ p := hp.2.two_le
    have hpe_pos : (0 : ℝ) < (p : ℝ) ^ ε :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hp_ge2) ε
    have hpe_gt1 : 1 < (p : ℝ) ^ ε := by
      rw [← Real.rpow_zero (p : ℝ)]
      apply Real.rpow_lt_rpow_of_exponent_lt
      · exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hp_ge2
      · exact hε
    exact div_pos hpe_pos (by linarith)
  refine ⟨D, hD_pos, fun n hn => ?_⟩
  rw [divisors_card_factorization n hn]
  set S := n.factorization.support with hS_def
  -- Split S into large primes (p^ε ≥ 2) and small primes (p^ε < 2)
  set S_l := S.filter (fun p : ℕ => 2 ≤ (p : ℝ) ^ ε) with hSl_def
  set S_s := S.filter (fun p : ℕ => (p : ℝ) ^ ε < 2) with hSs_def
  have hS_disj : Disjoint S_l S_s := by
    apply Finset.disjoint_left.mpr
    intro p h1 h2
    simp only [hSl_def, Finset.mem_filter] at h1
    simp only [hSs_def, Finset.mem_filter] at h2
    linarith [h1.2, h2.2]
  have hS_union : S_l ∪ S_s = S := by
    ext p
    simp only [Finset.mem_union, hSl_def, hSs_def, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_or_lt 2 ((p : ℝ) ^ ε) with h2 | h2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h, h2⟩
  -- Split τ(n) into large × small
  rw [← hS_union, Finset.prod_union hS_disj]
  -- Nat pow / rpow bridge: ((p:ℝ)^ε)^k = (p:ℝ)^(ε*k)
  have rpow_bridge : ∀ p : ℕ, ((p : ℝ) ^ ε) ^ (n.factorization p) =
      (p : ℝ) ^ (ε * n.factorization p) := fun p => by
    rw [← Real.rpow_natCast ((p : ℝ) ^ ε) (n.factorization p),
        ← Real.rpow_mul (Nat.cast_nonneg p)]
  -- Factorization product equals n^ε (§5)
  have hfact : ∏ p in S, (p : ℝ) ^ (ε * n.factorization p) = (n : ℝ) ^ ε :=
    factorization_rpow_eq n hn ε
  -- Bound for S_l: ∏ p in S_l, (e_p+1) ≤ ∏ p in S_l, p^{ε·e_p}
  have hSl_bound : ∏ p in S_l, ((n.factorization p : ℝ) + 1) ≤
      ∏ p in S_l, (p : ℝ) ^ (ε * n.factorization p) := by
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p hp
      simp only [hSl_def, Finset.mem_filter] at hp
      have h_succ := succ_le_rpow_large (n.factorization p) ((p : ℝ) ^ ε) hp.2
      rw [rpow_bridge] at h_succ
      linarith
  -- Bound for S_s: ∏ p in S_s, (e_p+1) ≤ D · ∏ p in S_s, p^{ε·e_p}
  have hSs_bound : ∏ p in S_s, ((n.factorization p : ℝ) + 1) ≤
      D * ∏ p in S_s, (p : ℝ) ^ (ε * n.factorization p) := by
    -- Pointwise bound: each factor (e_p+1) ≤ p^ε/(p^ε-1) · p^{ε·e_p}
    have h_factor : ∀ p ∈ S_s, (n.factorization p : ℝ) + 1 ≤
        (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) * (p : ℝ) ^ (ε * n.factorization p) := by
      intro p hp
      simp only [hSs_def, Finset.mem_filter] at hp
      obtain ⟨hmem, _⟩ := hp
      have hp_prime : p.Prime := by
        have hmem' : p ∈ n.factorization.support := hS_def ▸ hmem
        exact Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hmem')
      have hpe_gt1 : 1 < (p : ℝ) ^ ε := by
        rw [← Real.rpow_zero (p : ℝ)]
        apply Real.rpow_lt_rpow_of_exponent_lt
        · exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hp_prime.two_le
        · exact hε
      have h_succ := succ_le_rpow_small (n.factorization p) ((p : ℝ) ^ ε) hpe_gt1
      rw [rpow_bridge] at h_succ
      linarith
    calc ∏ p in S_s, ((n.factorization p : ℝ) + 1)
        ≤ ∏ p in S_s, ((p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) *
            (p : ℝ) ^ (ε * n.factorization p)) := by
              apply Finset.prod_le_prod
              · intro p _; positivity
              · exact h_factor
      _ = (∏ p in S_s, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1)) *
          ∏ p in S_s, (p : ℝ) ^ (ε * n.factorization p) := Finset.prod_mul_distrib
      _ ≤ D * ∏ p in S_s, (p : ℝ) ^ (ε * n.factorization p) := by
            apply mul_le_mul_of_nonneg_right _
              (Finset.prod_nonneg fun p _ =>
                Real.rpow_nonneg (Nat.cast_nonneg p) _)
            -- ∏ S_s coeff ≤ D = ∏ small_ps coeff (S_s ⊆ small_ps, all factors ≥ 1)
            have hDdef : D = ∏ p in small_ps,
                (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) := rfl
            rw [hDdef]
            have hsub : S_s ⊆ small_ps := by
              intro p hp
              simp only [hSs_def, Finset.mem_filter] at hp
              obtain ⟨hmem, h_small⟩ := hp
              have hp_prime : p.Prime := by
                have hmem' : p ∈ n.factorization.support := hS_def ▸ hmem
                exact Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hmem')
              -- p < B: from p^ε < 2 we get p < 2^{1/ε} ≤ ↑(ceil(2^{1/ε})) < ↑B
              have hp_lt_B : p < B := by
                have h1ε : (0 : ℝ) < 1 / ε := div_pos one_pos hε
                -- (p:ℝ) = ((p:ℝ)^ε)^{1/ε} < 2^{1/ε}
                have hpe_eq : ((p : ℝ) ^ ε) ^ (1 / ε) = (p : ℝ) := by
                  rw [← Real.rpow_mul (Nat.cast_nonneg p)]
                  have hmul : ε * (1 / ε) = 1 := by field_simp
                  rw [hmul, Real.rpow_one]
                have hp_real : (p : ℝ) < (2 : ℝ) ^ (1 / ε) := by
                  rw [← hpe_eq]
                  exact Real.rpow_lt_rpow
                    (Real.rpow_nonneg (Nat.cast_nonneg p) ε) h_small h1ε
                have h2 : (2 : ℝ) ^ (1 / ε) ≤ ↑(Nat.ceil ((2 : ℝ) ^ (1 / ε))) := Nat.le_ceil _
                have h3 : (p : ℝ) < ↑(Nat.ceil ((2 : ℝ) ^ (1 / ε))) :=
                  lt_of_lt_of_le hp_real h2
                have h4 : p < Nat.ceil ((2 : ℝ) ^ (1 / ε)) := by exact_mod_cast h3
                simp only [B]; omega
              simp only [small_ps, Finset.mem_filter, Finset.mem_range]
              exact ⟨hp_lt_B, hp_prime⟩
            have hge : ∀ p ∈ small_ps, p ∉ S_s →
                1 ≤ (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) := by
              intro p hp _
              simp only [small_ps, Finset.mem_filter] at hp
              have hp_ge2 : 2 ≤ p := hp.2.two_le
              have hpe_gt1 : 1 < (p : ℝ) ^ ε := by
                rw [← Real.rpow_zero (p : ℝ)]
                apply Real.rpow_lt_rpow_of_exponent_lt
                · exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hp_ge2
                · exact hε
              rw [le_div_iff₀ (by linarith)]
              linarith
            have hrest : 1 ≤ ∏ p in small_ps \ S_s,
                (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) := by
              refine Finset.prod_induction
                (fun p : ℕ => (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1)) (fun x => 1 ≤ x)
                ?_ le_rfl ?_
              · intro a b ha hb
                have h : (1 : ℝ) * 1 ≤ a * b :=
                  mul_le_mul ha hb (by norm_num) (by linarith)
                simpa using h
              · intro p hp
                exact hge p (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2
            have hsplit : ∏ p in small_ps, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) =
                (∏ p in small_ps \ S_s, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1)) *
                  ∏ p in S_s, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) := by
              rw [← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hsub]
            calc ∏ p in S_s, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1)
                = 1 * ∏ p in S_s, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) := by ring
              _ ≤ (∏ p in small_ps \ S_s, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1)) *
                    ∏ p in S_s, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) := by
                  apply mul_le_mul_of_nonneg_right hrest
                  apply Finset.prod_nonneg
                  intro p hp
                  have hpos : 0 < (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) := by
                    obtain ⟨hpS, _⟩ : p ∈ S ∧ (p : ℝ) ^ ε < 2 := by
                      simpa only [hSs_def, Finset.mem_filter] using hp
                    have hmem' : p ∈ n.factorization.support := hS_def ▸ hpS
                    have hp_prime :=
                      Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hmem')
                    have hpe : 1 < (p : ℝ) ^ ε := by
                      rw [← Real.rpow_zero (p : ℝ)]
                      exact Real.rpow_lt_rpow_of_exponent_lt
                        (by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hp_prime.two_le) hε
                    exact div_pos (by linarith) (by linarith)
                  linarith
              _ = ∏ p in small_ps, (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1) := hsplit.symm
  -- Combine: τ(n) ≤ (∏ S_l p^{ε·e}) · D · (∏ S_s p^{ε·e}) = D · n^ε
  calc (∏ p in S_l, ((n.factorization p : ℝ) + 1)) *
        (∏ p in S_s, ((n.factorization p : ℝ) + 1))
      ≤ (∏ p in S_l, (p : ℝ) ^ (ε * n.factorization p)) *
        (D * ∏ p in S_s, (p : ℝ) ^ (ε * n.factorization p)) :=
          mul_le_mul hSl_bound hSs_bound
            (Finset.prod_nonneg fun p _ =>
              by positivity)
            (Finset.prod_nonneg fun p _ =>
              Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ = D * ((∏ p in S_l, (p : ℝ) ^ (ε * n.factorization p)) *
              ∏ p in S_s, (p : ℝ) ^ (ε * n.factorization p)) := by ring
    _ = D * ∏ p in S, (p : ℝ) ^ (ε * n.factorization p) := by
          rw [← Finset.prod_union hS_disj, hS_union]
    _ = D * (n : ℝ) ^ ε := by rw [hfact]

/-- `a_n` on a squarefree argument is the product of `a_p` over its prime factors.
    Each exponent in the factorization is 1, and `a_prime_pow p 1 = a_p p`. -/
lemma a_n_squarefree_prod (n : ℕ) (hn : 0 < n) (hs : Squarefree n) :
    a_n n = ∏ p in n.factorization.support,
      if h : p.Prime then
        haveI : Fact p.Prime := ⟨h⟩
        a_p p
      else 1 := by
  have hn0 : n ≠ 0 := hn.ne'
  simp only [a_n, hn0, ite_false]
  rw [Finsupp.prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_prime : p.Prime :=
    Nat.prime_of_mem_primeFactors ((Nat.support_factorization n).symm ▸ hp)
  have he : n.factorization p = 1 := by
    have hle : n.factorization p ≤ 1 :=
      ((Nat.squarefree_iff_factorization_le_one hn0).mp hs) p
    have hne : n.factorization p ≠ 0 := (Finsupp.mem_support_iff).mp hp
    omega
  simp only [hp_prime, dite_true, he]
  rfl

/-- Squarefree `n` with every prime factor in the 84 checked primes.
    `|a_n n| ≤ 2^{ω(n)} √n = τ(n) √n ≤ D n^{1/2+ε}`.
    This does not bound `a_{p^k}` for `k ≥ 2`. It does not prove summability
    of the L-series. That still needs Hasse for every prime and the
    prime-power bound. -/
theorem BSD_an_squarefree_checked_bound
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 0 < n) (hs : Squarefree n)
    (hfac : ∀ p : ℕ, p ∈ n.primeFactors → p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    ∃ D : ℝ, 0 < D ∧ |(a_n n : ℝ)| ≤ D * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨D, hD, hτ⟩ := BSD_tau_bound_of_divisors ε hε
  have hn0 : n ≠ 0 := hn.ne'
  have hsq : ∀ p, n.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hn0).mp hs
  have hone : ∀ p ∈ n.factorization.support, n.factorization p = 1 := by
    intro p hp
    have hle := hsq p
    have hne : n.factorization p ≠ 0 := (Finsupp.mem_support_iff).mp hp
    omega
  have hprod_pow : ∏ p in n.factorization.support, p ^ n.factorization p = n := by
    simpa [Finsupp.prod] using Nat.factorization_prod_pow_eq_self hn0
  have hprod_p : ∏ p in n.factorization.support, p = n := by
    have hcongr : ∏ p in n.factorization.support, p ^ n.factorization p =
        ∏ p in n.factorization.support, p :=
      Finset.prod_congr rfl fun p hp => by rw [hone p hp, pow_one]
    exact hcongr.symm.trans hprod_pow
  have htau_card : (n.divisors.card : ℝ) = (2 : ℝ) ^ n.primeFactors.card := by
    have hcard := Nat.card_divisors hn0
    rw [← Nat.support_factorization] at hcard
    rw [hcard, finset_prod_cast]
    have htwo : ∏ p in n.factorization.support, (((n.factorization p + 1 : ℕ) : ℝ)) =
        ∏ _p in n.factorization.support, (2 : ℝ) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have : n.factorization p + 1 = 2 := by
        rw [hone p hp]
      simp [this]
    rw [htwo, Finset.prod_const, Nat.support_factorization]
  set S := n.factorization.support with hS
  let f : ℕ → ℤ := fun p =>
    if h : p.Prime then
      haveI : Fact p.Prime := ⟨h⟩
      a_p p
    else 1
  have habs : |(a_n n : ℝ)| ≤
      (2 : ℝ) ^ n.primeFactors.card * Real.sqrt (n : ℝ) := by
    have h_an : a_n n = ∏ p in S, f p := by
      simpa [f, hS] using a_n_squarefree_prod n hn hs
    have habsZ : |∏ p in S, f p| = ∏ p in S, |f p| := Finset.abs_prod _ _
    have hcast_abs : (Int.cast (R := ℝ) |a_n n|) = |(a_n n : ℝ)| := Int.cast_abs
    have hcast_prod :
        Int.cast (R := ℝ) (∏ p in S, |f p|) =
          ∏ p in S, Int.cast (R := ℝ) |f p| :=
      map_prod (Int.castRingHom ℝ) (fun p => |f p|) S
    have hpoint : ∀ p ∈ S, Int.cast (R := ℝ) |f p| ≤ 2 * Real.sqrt (p : ℝ) := by
      intro p hp
      have hp_pf : p ∈ n.primeFactors :=
        (Nat.support_factorization n) ▸ (hS.symm ▸ hp)
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
      haveI : Fact p.Prime := ⟨hp_prime⟩
      have hH := (BSD_Hasse_Forms_Equiv_84 p (hfac p hp_pf)).1
      have hf : f p = a_p p := by simp [f, hp_prime]
      rw [Int.cast_abs, hf]
      exact hH
    have hprod_le : ∏ p in S, Int.cast (R := ℝ) |f p| ≤
        ∏ p in S, (2 * Real.sqrt (p : ℝ)) :=
      Finset.prod_le_prod (fun _ _ => by positivity) hpoint
    have hsplit : ∏ p in S, (2 * Real.sqrt (p : ℝ)) =
        (∏ _p in S, (2 : ℝ)) * ∏ p in S, Real.sqrt (p : ℝ) :=
      Finset.prod_mul_distrib
    have htwo : ∏ _p in S, (2 : ℝ) = (2 : ℝ) ^ S.card := Finset.prod_const _
    have hsqrt_prod : ∏ p in S, Real.sqrt (p : ℝ) = Real.sqrt (n : ℝ) := by
      have hprodR : ∏ p in S, (p : ℝ) = (n : ℝ) := by
        rw [← finset_prod_cast S (fun p => p)]
        exact_mod_cast (hS ▸ hprod_p)
      simp_rw [Real.sqrt_eq_rpow]
      rw [← finset_prod_rpow S (fun p => (p : ℝ))
            (fun _ _ => Nat.cast_nonneg _) ((1 : ℝ) / 2), hprodR]
    have hcard : S.card = n.primeFactors.card := by
      rw [hS, Nat.support_factorization]
    calc |(a_n n : ℝ)|
        = Int.cast (R := ℝ) |a_n n| := hcast_abs.symm
      _ = Int.cast (R := ℝ) |∏ p in S, f p| := by rw [h_an]
      _ = Int.cast (R := ℝ) (∏ p in S, |f p|) := by rw [habsZ]
      _ = ∏ p in S, Int.cast (R := ℝ) |f p| := hcast_prod
      _ ≤ ∏ p in S, (2 * Real.sqrt (p : ℝ)) := hprod_le
      _ = (2 : ℝ) ^ S.card * ∏ p in S, Real.sqrt (p : ℝ) := by rw [hsplit, htwo]
      _ = (2 : ℝ) ^ n.primeFactors.card * Real.sqrt (n : ℝ) := by
          rw [hcard, hsqrt_prod]
  have hmul : (2 : ℝ) ^ n.primeFactors.card * Real.sqrt (n : ℝ) ≤
      D * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
    have hpow : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ε =
        (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
      rw [← Real.rpow_add (by exact_mod_cast hn) ((1 : ℝ) / 2) ε]
    have hsqrt_eq : Real.sqrt (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.sqrt_eq_rpow (n : ℝ)
    have htwo : (2 : ℝ) ^ n.primeFactors.card ≤ D * (n : ℝ) ^ ε := by
      rw [← htau_card]
      exact hτ n hn
    calc (2 : ℝ) ^ n.primeFactors.card * Real.sqrt (n : ℝ)
        = (2 : ℝ) ^ n.primeFactors.card * (n : ℝ) ^ ((1 : ℝ) / 2) := by rw [hsqrt_eq]
      _ ≤ (D * (n : ℝ) ^ ε) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_right htwo
          exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      _ = D * ((n : ℝ) ^ ε * (n : ℝ) ^ ((1 : ℝ) / 2)) := by ring
      _ = D * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
          rw [mul_comm ((n : ℝ) ^ ε), hpow]
  refine ⟨D, hD, ?_⟩
  exact habs.trans hmul

/-- Every integer in the checked list is prime. This is a `decide` on the
    existing list of 84 primes. It does not count points of `E143_Finset`. -/
theorem BSD_Finite_Hasse_CheckedPrimes_prime
    {p : ℕ} (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) : p.Prime := by
  have hp' : p ∈ BSD_Finite_Hasse_CheckedList := by
    simpa [BSD_Finite_Hasse_CheckedPrimes] using hp
  have hall : BSD_Finite_Hasse_CheckedList.all (fun n => decide (n.Prime)) = true := by
    native_decide
  exact of_decide_eq_true ((List.all_eq_true.mp hall) p hp')

/-- Factorization of a product of distinct primes is the indicator of that set. -/
lemma prod_distinct_primes_factorization {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (q : ℕ) :
    (∏ p in s, p).factorization q = if q ∈ s then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp [Nat.factorization_one]
  | insert ha ih =>
    rename_i a s
    have ha_prime : a.Prime := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hprod_pos : 0 < ∏ p in s, p :=
      Finset.prod_pos fun p hp => (hs' p hp).pos
    rw [Finset.prod_insert ha, Nat.factorization_mul ha_prime.ne_zero hprod_pos.ne']
    have hih := ih hs'
    simp only [Finsupp.add_apply, ha_prime.factorization, Finsupp.single_apply, hih,
      Finset.mem_insert]
    rcases eq_or_ne q a with hqa | hqa
    · subst hqa
      simp [ha]
    · have hqa' : ¬ a = q := Ne.symm hqa
      by_cases hqs : q ∈ s
      · simp [hqa, hqa', hqs]
      · simp [hqa, hqa', hqs]

/-- Squarefree `n` supported on the 84 checked primes divide the product of
    those primes, so there are finitely many of them. The Dirichlet series
    over that finite set is summable for every real exponent, in particular
    whenever `σ > 3/2`. The hypothesis `3/2 < σ` is the threshold asked for
    the truncated series. It is not used: finiteness is the reason the sum
    converges. Prime powers `p^k` with `k ≥ 2` are excluded. This is not
    `BSD_LSeriesSummable_OPEN`, which quantifies over every positive integer. -/
theorem BSD_squarefree_checked_dirichlet_summable
    (σ : ℝ) (_hσ : (3 : ℝ) / 2 < σ) :
    Summable fun n : ℕ =>
      if _h : 0 < n ∧ Squarefree n ∧
          (∀ p ∈ n.primeFactors, p ∈ BSD_Finite_Hasse_CheckedPrimes) then
        |(a_n n : ℝ)| / (n : ℝ) ^ σ
      else 0 := by
  let P : ℕ := ∏ p in BSD_Finite_Hasse_CheckedPrimes, p
  have hP : P ≠ 0 := by
    refine (Finset.prod_pos fun p hp => (BSD_Finite_Hasse_CheckedPrimes_prime hp).pos).ne'
  apply summable_of_ne_finset_zero (s := P.divisors)
  intro n hn
  by_cases h :
      0 < n ∧ Squarefree n ∧
        (∀ p ∈ n.primeFactors, p ∈ BSD_Finite_Hasse_CheckedPrimes)
  · exfalso
    obtain ⟨hn0, hs, hfac⟩ := h
    have hle : n.factorization ≤ P.factorization := by
      rw [Finsupp.le_def]
      intro q
      by_cases hq : q.Prime
      · have hnfac : n.factorization q = if q ∈ n.primeFactors then 1 else 0 := by
          by_cases hmem : q ∈ n.primeFactors
          · have he : n.factorization q = 1 := by
              have hle1 : n.factorization q ≤ 1 :=
                ((Nat.squarefree_iff_factorization_le_one hn0.ne').mp hs) q
              have hne : n.factorization q ≠ 0 :=
                (Finsupp.mem_support_iff).mp
                  ((Nat.support_factorization n).symm ▸ hmem)
              omega
            simp [hmem, he]
          · have hndvd : ¬ q ∣ n := by
              intro hdvd
              exact hmem ((Nat.mem_primeFactors).mpr ⟨hq, hdvd, hn0.ne'⟩)
            simp [hmem, Nat.factorization_eq_zero_of_not_dvd hndvd]
        have hPfac : P.factorization q =
            if q ∈ BSD_Finite_Hasse_CheckedPrimes then 1 else 0 :=
          prod_distinct_primes_factorization
            (fun p hp => BSD_Finite_Hasse_CheckedPrimes_prime hp) q
        rw [hnfac, hPfac]
        by_cases hmem : q ∈ n.primeFactors
        · simp [hmem, hfac q hmem]
        · simp [hmem]
      · rw [Nat.factorization_eq_zero_of_non_prime n hq,
            Nat.factorization_eq_zero_of_non_prime P hq]
    have hdvd : n ∣ P := (Nat.factorization_le_iff_dvd hn0.ne' hP).mp hle
    have hn_mem : n ∈ P.divisors := by
      rw [Nat.mem_divisors]
      exact ⟨hdvd, hP⟩
    exact hn hn_mem
  · rw [dif_neg h]

end Towers.BSD
