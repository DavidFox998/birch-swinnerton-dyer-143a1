/-!
# BSD genesis-780: Closing Avenue 3 and BSD_isBigO_to_LSeries_OPEN

**Module**: `BSD/BSD_Genesis780_CLOSED.lean`
**Imports**: `Towers.BSD.BSD_Genesis779_CLOSED`
**sorry count**: 0
**axioms**: {propext, Classical.choice, Quot.sound}

## Proof chain this batch

Four items:

  **Avenue 3 — Finsupp product monotonicity (BSD_Finsupp_prod_le_OPEN)**:
    §1 BSD_Finsupp_prod_le_close — PROVED all n
        (Finset.prod_le_prod nonneg + Gate 1 pointwise via split_ifs)

  **Avenue 4 — isBigO to LSeriesSummable bridge (BSD_isBigO_to_LSeries_OPEN)**:
    §2 BSD_isBigO_to_LSeries_close — PROVED unconditionally
        (LSeriesSummable_of_le_const_mul_rpow + Summable.comp_injective
         + LSeries.term_of_ne_zero; ε₀ = (Re(s)-3/2)/2 chooses the comparison exponent)

  **Combined chains**:
    §3 BSD_aNBound_all_n_v3    — ∀ n, BSD_aNBound_OPEN n, Gate 1 ONLY
        (consolidates all three proved bridges: genesis-779 §2 + §8, genesis-780 §1)
    §4 BSD_LSeriesSummable_v3  — BSD_LSeriesSummable_OPEN, Gate 1 + TauBound ONLY
        (was 6 hypotheses in genesis-778; now 2)

## Gap inventory after genesis-780

PROVED (unconditional or conditional Gate 1):
  - BSD_aNBound_Finsupp_bridge_OPEN ∀ n (genesis-779 §2, unconditional)
  - BSD_tau_sqrt_OPEN n for n ≥ 1  (genesis-779 §8, unconditional)
  - BSD_Finsupp_prod_le_OPEN ∀ n   (genesis-780 §1, conditional Gate 1)
  - BSD_isBigO_to_LSeries_OPEN     (genesis-780 §2, unconditional)

OPEN (genuine mathematical gaps, no timeline):
  - BSD_WeilHasse_Weierstrass_OPEN  Gate 1: Hasse-Weil bound (Clay-grade)
  - BSD_LFunctionIsLinFunc_OPEN     Gate 2: Hecke/Mellin (Clay-grade)
  - BSD_TauBound_OPEN               τ(n) = O(n^ε), not in Mathlib v4.12.0
  - BSD_{NT,Reg,SHA,Coeff,Period,Tamagawa,Torsion,Generator}_OPEN  (8 BSD formula surfaces)

0 sorry.  Classical trio + Gate 1 hypothesis where noted.
BSD: OPEN.  No Clay claim.
-/

import Towers.BSD.BSD_Genesis779_CLOSED
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open BigOperators Real Nat ArithmeticFunction

namespace Towers.BSD

/-! ## §1. BSD_Finsupp_prod_le_close — Avenue 3 CLOSED -/

/-- **PROVED** (0 sorry, conditional Gate 1):
    n.factorization.prod |a_{p^e}| ≤ n.factorization.prod (e+1)(√p)^e.

    Proof:
    • Nonneg:     ∀ p ∈ support, 0 ≤ |a_{p^e}|  (abs_nonneg; else branch gives 1 ≥ 0)
    • Pointwise:  ∀ p ∈ support, |a_{p^e}| ≤ (e+1)(√p)^e
                  — p ∈ n.factorization.support → p.Prime (Nat.support_factorization)
                  — split_ifs: true branch closes via hGate1 p ⟨h⟩ (n.factorization p)
                  — false branch: contradiction with p.Prime (which we just proved)
    Apply Finset.prod_le_prod (Mathlib.Algebra.Order.BigOperators.Ring.Finset L36). -/
theorem BSD_Finsupp_prod_le_close (n : ℕ) : BSD_Finsupp_prod_le_OPEN n := by
  intro hGate1
  simp only [Finsupp.prod]
  apply Finset.prod_le_prod
  · -- h0: 0 ≤ (each LHS factor)
    intro p _
    split_ifs with h
    · exact abs_nonneg _
    · norm_num
  · -- h1: (each LHS factor) ≤ (each RHS factor)
    intro p hp
    have hprime : p.Prime :=
      Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    haveI hfact : Fact p.Prime := ⟨hprime⟩
    split_ifs with h
    · -- p.Prime branch: |a_{p^e}| ≤ (e+1)(√p)^e  by Gate 1
      exact hGate1 p ⟨h⟩ (n.factorization p)
    · -- ¬p.Prime branch: contradicts hprime
      exact absurd hprime h

/-! ## §2. BSD_isBigO_to_LSeries_close — Avenue 4 CLOSED -/

/-- **PROVED** (0 sorry, unconditional):
    BSD_isBigO_to_LSeries_OPEN.

    Given the uniform pointwise bound `|a_n n| ≤ C_ε · n^{1/2+ε}` for all ε > 0 and n : ℕ+,
    prove BSD_LSeriesSummable_OPEN = `∀ s : ℂ, 3/2 < Re(s) → Summable (ℕ+ ↦ a_n n / n^s)`.

    Proof sketch:
    (A) For each s with Re(s) > 3/2, choose ε₀ := (Re(s) - 3/2)/2 > 0.
    (B) Obtain C₀ with `|a_n n| ≤ C₀ · n^{1/2+ε₀}` for all n : ℕ+.
    (C) Set x := 3/2 + ε₀ < Re(s) and note x - 1 = 1/2 + ε₀.
        Apply `LSeriesSummable_of_le_const_mul_rpow` (LSeries/Basic.lean L313) to get
        `LSeriesSummable (fun n : ℕ ↦ (a_n n : ℂ)) s`.
    (D) Pull back via `Summable.comp_injective Subtype.val_injective` to ℕ+,
        then simplify `LSeries.term f s ↑n = f ↑n / ↑n^s` via `term_of_ne_zero n.pos.ne'`. -/
theorem BSD_isBigO_to_LSeries_close : BSD_isBigO_to_LSeries_OPEN := by
  intro h_bound
  intro s hs
  -- (A) Choose ε₀ = (Re(s) - 3/2) / 2 > 0
  set ε₀ := (s.re - 3 / 2) / 2 with hε₀_def
  have hε₀_pos : (0 : ℝ) < ε₀ := by unfold_let ε₀; linarith
  -- (B) Extract the uniform bound for this ε₀
  obtain ⟨C, hC_pos, hC_bound⟩ := h_bound ε₀ hε₀_pos
  -- x := 3/2 + ε₀ satisfies x < Re(s) (by construction)
  have hx_lt : 3 / 2 + ε₀ < s.re := by unfold_let ε₀; linarith
  -- And x - 1 = 1/2 + ε₀ (matches h_bound exponent)
  have hexp : (3 / 2 + ε₀ : ℝ) - 1 = 1 / 2 + ε₀ := by ring
  -- (C) Prove LSeriesSummable over ℕ
  have hLS : LSeriesSummable (fun n : ℕ => (a_n n : ℂ)) s := by
    apply LSeriesSummable_of_le_const_mul_rpow hx_lt
    refine ⟨C, fun n hn => ?_⟩
    have hpos : 0 < n := Nat.pos_of_ne_zero hn
    -- Norm cast: ‖(a_n n : ℂ)‖ = |(a_n n : ℝ)|
    -- (a_n n : ℤ) → ℂ equals (a_n n : ℤ) → ℝ → ℂ, so norm is the real absolute value
    have hcast : ‖(a_n n : ℂ)‖ = |(a_n n : ℝ)| := by
      have heq : (a_n n : ℂ) = ((a_n n : ℝ) : ℂ) := by norm_cast
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
    -- Use the bound from h_bound at ⟨n, hpos⟩ : ℕ+
    have hbound_n : |(a_n n : ℝ)| ≤ C * (n : ℝ) ^ (1 / 2 + ε₀) :=
      hC_bound ⟨n, hpos⟩
    -- Rewrite exponent: (3/2 + ε₀) - 1 = 1/2 + ε₀
    rw [hcast, hexp]
    exact hbound_n
  -- (D) Convert LSeriesSummable (ℕ) to Summable (ℕ+)
  simp only [LSeriesSummable] at hLS
  -- Pull back along PNat.val : ℕ+ ↪ ℕ (injective via Subtype.val_injective)
  have h_pos_summ : Summable (fun n : ℕ+ =>
      LSeries.term (fun n : ℕ => (a_n n : ℂ)) s n.val) :=
    hLS.comp_injective Subtype.val_injective
  -- Simplify LSeries.term at n.val (which is ≠ 0 since n : ℕ+)
  apply h_pos_summ.congr
  intro n
  simp only [Function.comp, LSeries.term_of_ne_zero n.pos.ne']

/-! ## §3. BSD_aNBound_all_n_v3 — Gate 1 is the only remaining hypothesis -/

/-- **PROVED** (0 sorry): ∀ n, BSD_aNBound_OPEN n, conditional on Gate 1 ONLY.

    Consolidates all three proved bridges:
    • BSD_aNBound_Finsupp_bridge_close  (genesis-779 §2, Avenue 1, unconditional)
    • BSD_Finsupp_prod_le_close         (genesis-780 §1, Avenue 3, cond Gate 1)
    • BSD_tau_sqrt_close_pos            (genesis-779 §8, Avenue 2, n ≥ 1 only)

    Remaining genuine gap:
    • Gate 1 = BSD_PrimePowBound_OPEN = BSD_WeilHasse_Weierstrass_OPEN (Hasse-Weil). -/
theorem BSD_aNBound_all_n_v3
    (hGate1 : ∀ (q : ℕ) (hq : Fact q.Prime) (j : ℕ), BSD_PrimePowBound_OPEN q j) :
    ∀ n : ℕ, BSD_aNBound_OPEN n :=
  BSD_aNBound_all_n_v2 hGate1
    BSD_aNBound_Finsupp_bridge_close
    BSD_Finsupp_prod_le_close
    BSD_tau_sqrt_close_pos

/-! ## §4. BSD_LSeriesSummable_v3 — Gate 1 + TauBound only -/

/-- **PROVED** (0 sorry): BSD_LSeriesSummable_OPEN, conditional on Gate 1 + TauBound.

    Hypothesis count reduction:
      genesis-778 BSD_LSeriesSummable_conditional : 6 hypotheses
        (Gate1 + bridge1 + prod + tau_sq + TauBound + isBigO)
      genesis-780 BSD_LSeriesSummable_v3 : 2 hypotheses
        (Gate1 + TauBound)

    All four bridges now proved — only genuine mathematical gaps remain:
    • Gate 1 (BSD_PrimePowBound_OPEN): Hasse-Weil spectral bound, Clay-grade
    • BSD_TauBound_OPEN: τ(n) = O(n^ε) for all ε > 0 (Dirichlet hyperbola, not in Mathlib) -/
theorem BSD_LSeriesSummable_v3
    (hGate1  : ∀ (q : ℕ) (hq : Fact q.Prime) (j : ℕ), BSD_PrimePowBound_OPEN q j)
    (htau_bd : BSD_TauBound_OPEN) :
    BSD_LSeriesSummable_OPEN :=
  BSD_isBigO_to_LSeries_close (fun ε hε =>
    BSD_aNBound_times_tau_isBigO
      (BSD_aNBound_all_n_v3 hGate1)
      htau_bd ε hε)

end Towers.BSD
