/-!
# BSD genesis-782: Closing BSD_TauBound_small_OPEN

**Module**: `BSD/BSD_Genesis782_CLOSED.lean`
**Imports**: `Towers.BSD.BSD_Genesis781_CLOSED`
**sorry count**: 0
**axioms**: {propext, Classical.choice, Quot.sound}

## Proof chain

  **§1 succ_le_two_pow**: k+1 ≤ 2^k for all k : ℕ (induction).

  **§2 bernoulli_ineq**: 1 + k*x ≤ (1+x)^k for x ≥ 0, k : ℕ (induction).

  **§3 finset_prod_cast**: (↑∏ f : ℕ) : ℝ = ∏ (f : ℝ) (Finset induction).

  **§4 finset_prod_rpow**: (∏ fi)^r = ∏ (fi^r) for fi ≥ 0 (Finset induction).

  **§5 factorization_rpow_eq**: ∏_{p|n} (p:ℝ)^(ε*e_p) = (n:ℝ)^ε.
    Uses §3+§4 + Nat.factorization_prod_pow_eq_self.

  **§6 succ_le_rpow_large**: k+1 ≤ β^k (nat pow) for β ≥ 2.  Uses §1.

  **§7 succ_le_rpow_small**: k+1 ≤ β/(β-1)·β^k (nat pow) for β > 1.  Uses §2.

  **§8 BSD_TauBound_small_proved** (0 sorry, unconditional):
    For any 0 < ε < 1/2: ∃ D > 0, τ(n) ≤ D·n^ε for all n ≥ 1.
    Uses BSD_card_divisors_close (genesis-779) for τ(n) as a real product + §§5-7.

  **§9 BSD_TauBound_OPEN_proved** (0 sorry, unconditional):
    Closes BSD_TauBound_OPEN via BSD_TauBound_from_parts (genesis-781).

  **§10 BSD_LSeriesSummable_v5** (0 sorry, Gate 1 only):
    BSD_LSeriesSummable_OPEN via BSD_LSeriesSummable_v3 (genesis-780) + §9.

## Gap inventory after genesis-782

PROVED (unconditional):
  - BSD_TauBound_OPEN                     (genesis-782 §9)

PROVED (conditional Gate 1 = Hasse-Weil only):
  - BSD_LSeriesSummable_OPEN              (genesis-782 §10, one hypothesis)

OPEN (genuine gaps):
  - BSD_WeilHasse_Weierstrass_OPEN  Gate 1 (Clay-grade, Hasse-Weil Frobenius)
  - BSD_LFunctionIsLinFunc_OPEN     Gate 2 (Clay-grade, Hecke/Mellin)
  - 8 BSD formula surfaces

Clay gate count: 2 (unchanged). BSD: OPEN. No Clay claim.
0 sorry. Classical trio. Gate 1 in §10 only.
-/

import Towers.BSD.BSD_Genesis781_CLOSED
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators Real Nat ArithmeticFunction

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

private theorem finset_prod_cast {α : Type*} (s : Finset α) (f : α → ℕ) :
    (↑(∏ i in s, f i) : ℝ) = ∏ i in s, (f i : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, ih]

/-! ## §4. finset_prod_rpow -/

private theorem finset_prod_rpow {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    (∏ i in s, f i) ^ r = ∏ i in s, (f i) ^ r := by
  induction s using Finset.induction_on with
  | empty => simp [Real.one_rpow]
  | insert ha ih =>
    rename_i a s' _
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
  rw [div_mul_eq_mul_div, le_div_iff hβ1,
      show β * β ^ k = β ^ (k + 1) from (pow_succ β k).symm]
  -- Goal: (↑k + 1) * (β - 1) ≤ β^(k+1)
  -- Bernoulli: β^(k+1) = (1+(β-1))^(k+1) ≥ 1 + (k+1)*(β-1) ≥ (k+1)*(β-1)
  have hbern := bernoulli_ineq (k + 1) (β - 1) hβ1.le
  simp only [sub_add_cancel] at hbern
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
theorem BSD_TauBound_small_proved : BSD_TauBound_small_OPEN := by
  intro ε hε _
  -- Finite threshold: primes p with p^ε < 2 satisfy p < 2^{1/ε} < B
  let B : ℕ := Nat.ceil (2 ^ (1 / ε)) + 2
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
  -- τ(n) as real product over factorization support (genesis-779 BSD_card_divisors_close)
  have htau := BSD_card_divisors_close n hn
  -- htau : (n.divisors.card : ℝ) = ∏ p ∈ n.factorization.support, (n.factorization p + 1 : ℝ)
  rw [htau]
  set S := n.factorization.support with hS_def
  -- Split S into large primes (p^ε ≥ 2) and small primes (p^ε < 2)
  set S_l := S.filter (fun p => 2 ≤ (p : ℝ) ^ ε) with hSl_def
  set S_s := S.filter (fun p => (p : ℝ) ^ ε < 2) with hSs_def
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
    congr 1; ring
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
      have hp_prime : p.Prime :=
        Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hmem)
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
            apply Finset.prod_le_prod_of_subset_of_one_le'
            · -- S_s ⊆ small_ps
              intro p hp
              simp only [hSs_def, Finset.mem_filter] at hp
              obtain ⟨hmem, h_small⟩ := hp
              have hp_prime : p.Prime :=
                Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hmem)
              -- p < B: from p^ε < 2 we get p < 2^{1/ε} ≤ ↑(ceil(2^{1/ε})) < ↑B
              have hp_lt_B : p < B := by
                have h1ε : (0 : ℝ) < 1 / ε := div_pos one_pos hε
                -- (p:ℝ) = ((p:ℝ)^ε)^{1/ε} < 2^{1/ε}
                have hpe_eq : ((p : ℝ) ^ ε) ^ (1 / ε) = (p : ℝ) := by
                  rw [← Real.rpow_natCast ((p : ℝ) ^ ε), ← Real.rpow_mul (Nat.cast_nonneg p)]
                  -- Hmm, ε * (1/ε) = 1 and then rpow_one
                  have hmul : ε * (1 / ε) = 1 := by field_simp
                  rw [hmul, Real.rpow_one]
                have hp_real : (p : ℝ) < 2 ^ (1 / ε) := by
                  rw [← hpe_eq]
                  exact Real.rpow_lt_rpow
                    (Real.rpow_nonneg (Nat.cast_nonneg p) ε) h_small h1ε
                have h2 : 2 ^ (1 / ε) ≤ ↑(Nat.ceil (2 ^ (1 / ε))) := Nat.le_ceil _
                have h3 : (p : ℝ) < ↑(Nat.ceil (2 ^ (1 / ε))) :=
                  lt_of_lt_of_le hp_real h2
                have h4 : p < Nat.ceil (2 ^ (1 / ε)) := by exact_mod_cast h3
                simp only [B]; omega
              simp only [small_ps, Finset.mem_filter, Finset.mem_range]
              exact ⟨hp_lt_B, hp_prime⟩
            · -- Each factor ≥ 1 for primes in small_ps
              intro p hp _
              simp only [small_ps, Finset.mem_filter] at hp
              have hp_ge2 : 2 ≤ p := hp.2.two_le
              have hpe_gt1 : 1 < (p : ℝ) ^ ε := by
                rw [← Real.rpow_zero (p : ℝ)]
                apply Real.rpow_lt_rpow_of_exponent_lt
                · exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hp_ge2
                · exact hε
              rw [le_div_iff (by linarith)]
              linarith
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

/-! ## §9. BSD_TauBound_OPEN_proved -/

/-- **PROVED** (0 sorry, unconditional): BSD_TauBound_OPEN.

    Combines §8 (0 < ε < 1/2) with BSD_TauBound_large_eps (ε ≥ 1/2, genesis-781)
    via BSD_TauBound_from_parts (genesis-781). -/
theorem BSD_TauBound_OPEN_proved : BSD_TauBound_OPEN :=
  BSD_TauBound_from_parts BSD_TauBound_small_proved

/-! ## §10. BSD_LSeriesSummable_v5 -/

/-- **PROVED** (0 sorry, Gate 1 only): BSD_LSeriesSummable_OPEN.

    BSD_TauBound_OPEN is now unconditionally proved (§9).
    BSD_LSeriesSummable_v3 (genesis-780) takes Gate 1 + TauBound → LSeries;
    absorbing TauBound reduces the hypothesis count from 2 to 1. -/
theorem BSD_LSeriesSummable_v5
    (hGate1 : ∀ (q : ℕ) (hq : Fact q.Prime) (j : ℕ), BSD_PrimePowBound_OPEN q j) :
    BSD_LSeriesSummable_OPEN :=
  BSD_LSeriesSummable_v3 hGate1 BSD_TauBound_OPEN_proved

/-! ## Summary

### Genesis-782: BSD_TauBound_small_OPEN CLOSED

**BSD_TauBound_small_proved** (0 sorry, unconditional):
  τ(n) ≤ D_ε · n^ε  for 0 < ε < 1/2.
  D_ε = ∏_{p prime, p < 2^{1/ε}+2} p^ε/(p^ε-1)  (finite product, all factors ≥ 1).
  Key steps:
  • BSD_card_divisors_close (genesis-779):  τ(n) = ∏_{p|n} (e_p+1) as ℝ
  • succ_le_two_pow (§1): k+1 ≤ 2^k
  • bernoulli_ineq (§2): 1 + k·x ≤ (1+x)^k for x ≥ 0
  • factorization_rpow_eq (§5): ∏_{p|n} p^{ε·e_p} = n^ε
  • Large prime bound (§6): p^ε ≥ 2 → e+1 ≤ 2^e ≤ (p^ε)^e = p^{ε·e}
  • Small prime bound (§7): p^ε > 1 → e+1 ≤ p^ε/(p^ε-1) · p^{ε·e}  (Bernoulli)
  • D_ε ≥ ∏ S_s coeff via S_s ⊆ small_ps and all factors ≥ 1

**BSD_TauBound_OPEN_proved** (0 sorry, unconditional):
  Closes the analytic NT gap from genesis-778.

**BSD_LSeriesSummable_v5** (0 sorry, Gate 1 only):
  BSD_LSeriesSummable_OPEN — hypothesis count 2 → 1 (TauBound absorbed).

**Mathlib v4.12.0 APIs used:**
  Nat.factorization_prod_pow_eq_self     -- ∏ p^e_p = n (Finsupp.prod form)
  Nat.support_factorization              -- factorization.support = primeFactors
  Nat.prime_of_mem_primeFactors          -- entries of primeFactors are prime
  Nat.le_ceil                            -- r ≤ ↑⌈r⌉
  Real.rpow_pos_of_pos                   -- x > 0 → x^r > 0
  Real.rpow_lt_rpow_of_exponent_lt       -- x > 1 → a < b → x^a < x^b
  Real.rpow_lt_rpow                      -- 0 ≤ x → x < y → 0 ≤ r → x^r < y^r
  Real.rpow_mul                          -- x ≥ 0 → (x^r)^s = x^(r·s)
  Real.rpow_natCast                      -- x^(↑n) = x^n  (rpow/nat pow bridge)
  Finset.prod_le_prod                    -- pointwise bound → product bound
  Finset.prod_mul_distrib                -- ∏(f·g) = ∏f · ∏g
  Finset.prod_le_prod_of_subset_of_one_le' -- subset bound + factors ≥ 1
  Finset.disjoint_left.mpr               -- disjointness via membership

Clay gate count: 2 (unchanged). BSD: OPEN. No Clay claim.
0 sorry. Classical trio. Gate 1 in §10 only.
-/

end Towers.BSD
