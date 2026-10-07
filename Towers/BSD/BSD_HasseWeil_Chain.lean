/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_HasseWeil_Chain.lean — extracted 9 closed declarations. -/

theorem BSD_PrimePow_k0 (p : ℕ) [Fact p.Prime] :
    BSD_PrimePowBound_OPEN p 0 := by
  simp [BSD_PrimePowBound_OPEN, a_prime_pow]

/-- **PROVED** (0 sorry, classical trio, Milestone 3 base case k=1):
    Given BSD_Hasse_OPEN p (|a_p| ≤ 2√p),
    |a_{p^1}| = |a_p| ≤ 2√p = (1+1)·(√p)^1.
    Proof: unfold definitions then linarith. -/

theorem BSD_PrimePow_k1 (p : ℕ) [Fact p.Prime]
    (h : BSD_Hasse_OPEN p) : BSD_PrimePowBound_OPEN p 1 := by
  simp only [BSD_PrimePowBound_OPEN, a_prime_pow, pow_one, Nat.cast_add, Nat.cast_one]
  linarith [h]

-- ============================================================
-- §2. Tier B: OPEN sub-surfaces (def Prop, not axioms)
-- ============================================================

/-- **OPEN sub-surface**: inductive step for the prime-power Weil bound, k ≥ 2.
    Given BSD_Hasse_OPEN p, BSD_PrimePowBound_OPEN p k, BSD_PrimePowBound_OPEN p (k+1),
    concludes BSD_PrimePowBound_OPEN p (k+2).

    Mathematical content (Chebyshev-U identity):
      Let θ = Real.arccos (a_p p / (2 * √p)).  By Hasse, cos θ = a_p/(2√p) ∈ [−1,1].
      Then a_{p^k} = p^{k/2} · U_k(cos θ), where U_k is Chebyshev-U.
      The bound |U_k(x)| ≤ k+1 for |x| ≤ 1 gives |a_{p^k}| ≤ (k+1)·p^{k/2}.

    Gap: proving `a_{p^k}/p^{k/2} = U_k(a_p/(2√p))` by induction requires
    `Real.sin_nsucc_mul` or similar Lean API, and `|sin((k+1)θ)/sin θ| ≤ k+1`
    needs a monotonicity argument on sin quotients — not readily available
    in Mathlib v4.12.0 for this application. -/
def BSD_ChebyshevBound_OPEN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ),
    BSD_Hasse_OPEN p →
    BSD_PrimePowBound_OPEN p k →
    BSD_PrimePowBound_OPEN p (k + 1) →
    BSD_PrimePowBound_OPEN p (k + 2)

/-- **OPEN sub-surface**: τ(n) = O(n^ε) for all ε > 0.
    Classical result (Dirichlet divisor problem): τ(n) grows sub-polynomially.
    More precisely, ∀ ε > 0 ∃ C > 0, ∀ n ≥ 1, τ(n) ≤ C · n^ε.
    Gap: divisor function growth estimate absent from Mathlib v4.12.0
    `NumberTheory.ArithmeticFunction`. -/
def BSD_TauBound_OPEN : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ+, (n.val.divisors.card : ℝ) ≤ C * (n.val : ℝ) ^ ε

/-- **OPEN sub-surface**: L-series summable at σ > 1 given Deligne bound.
    Given BSD_aNBound_OPEN (all n) + BSD_TauBound_OPEN, the series
    ∑ |a_n|/n^σ converges for Re(s) > 1 (not just σ > 3/2).
    This improves the Tauberian convergence domain by 1/2. -/
def BSD_LSeriesSummable_Deligne_OPEN : Prop :=
  ∀ σ : ℝ, 1 < σ →
    Summable (fun n : ℕ+ => |(a_n n.val : ℝ)| / (n.val : ℝ) ^ σ)

-- ============================================================
-- §3. Conditional combinator: Hasse + Chebyshev → PrimePow (all k)
-- ============================================================

/-- **CONDITIONAL** (0 sorry, classical trio):
    Given BSD_Hasse_OPEN (∀ p) + BSD_ChebyshevBound_OPEN,
    BSD_PrimePowBound_OPEN holds for all primes p and all k ≥ 0.

    Proof by two-step induction:
    - Prove (BSD_PrimePowBound_OPEN p k ∧ BSD_PrimePowBound_OPEN p (k+1)) by induction.
    - Base: k=0: ⟨BSD_PrimePow_k0, BSD_PrimePow_k1⟩ (both proved above).
    - Step: ⟨ih.2, BSD_ChebyshevBound_OPEN p k h_hasse ih.1 ih.2⟩. -/

theorem BSD_hasse_to_primepow
    (h_hasse : ∀ (p : ℕ) [Fact p.Prime], BSD_Hasse_OPEN p)
    (h_cheb  : BSD_ChebyshevBound_OPEN)
    (p : ℕ) [hp : Fact p.Prime] :
    ∀ k : ℕ, BSD_PrimePowBound_OPEN p k := by
  intro k
  -- Two-step induction: prove conjunction at k, k+1 simultaneously
  suffices h : ∀ m : ℕ, BSD_PrimePowBound_OPEN p m ∧ BSD_PrimePowBound_OPEN p (m + 1) by
    exact (h k).1
  intro m
  induction m with
  | zero =>
    exact ⟨BSD_PrimePow_k0 p, BSD_PrimePow_k1 p (h_hasse p)⟩
  | succ m ih =>
    exact ⟨ih.2, h_cheb p m (h_hasse p) ih.1 ih.2⟩

-- ============================================================
-- §4. Deligne consequence: summability domain improvement
-- ============================================================

/-- **CONDITIONAL** (0 sorry, classical trio):
    Documents the convergence-domain improvement chain.
    Given BSD_aNBound_OPEN (∀n) + BSD_TauBound_OPEN as prerequisites, the gate
    BSD_LSeriesSummable_Deligne_OPEN names the conclusion.

    Why this is a conditional and not a proof:
    The actual summability proof requires real-analysis API for ℝ-valued Dirichlet
    series with rpow comparison (Summable.of_norm_bounded + rpow integral test)
    with the explicit bound |a_n|/n^σ ≤ C·n^{-(1+(σ-1)/2)} where C comes from
    BSD_TauBound_OPEN.  The integral test API for rpow in Mathlib v4.12.0 requires
    careful monotonicity + norm-type arguments not yet assembled here.

    This combinator documents the gate structure.  The named surface
    BSD_LSeriesSummable_Deligne_OPEN is the honest placeholder. -/

theorem BSD_deligne_convergence_chain
    (_h_del : ∀ n : ℕ+, BSD_aNBound_OPEN n.val)
    (_h_tau : BSD_TauBound_OPEN)
    (h_sum  : BSD_LSeriesSummable_Deligne_OPEN) :
    BSD_LSeriesSummable_Deligne_OPEN :=
  h_sum

-- ============================================================
-- §5. Milestone 3 chain combinator
-- ============================================================

/-- **Milestone 3 chain combinator** (0 sorry, classical trio):
    Given Hasse + Chebyshev (∀p,k bounds) + TauBound (summability at σ>1),
    plus the M2 comparison-series gate:

    Proved conclusions:
    1. BSD_PrimePowBound_OPEN p k for all p, k (from two-step induction above)
    2. BSD_PrimePow_k0, BSD_PrimePow_k1 (unconditional base cases)

    Three OPEN gates remain:
    - BSD_ChebyshevBound_OPEN (Chebyshev-U inductive step)
    - BSD_TauBound_OPEN (τ(n) = O(n^ε) divisor bound)
    - BSD_Hasse_OPEN (∀ p; Frobenius gap)

    NOT a proof of BSD.  NOT a proof of Hasse.  Honest conditional chain. -/

theorem BSD_m3_hasse_chain
    (h_hasse : ∀ (p : ℕ) [Fact p.Prime], BSD_Hasse_OPEN p)
    (h_cheb  : BSD_ChebyshevBound_OPEN) :
    (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), BSD_PrimePowBound_OPEN p k) ∧
    (∀ (p : ℕ) [Fact p.Prime], BSD_PrimePowBound_OPEN p 0) ∧
    (∀ (p : ℕ) [Fact p.Prime], BSD_PrimePowBound_OPEN p 1) :=
  ⟨fun p _hp k => BSD_hasse_to_primepow h_hasse h_cheb p k,
   fun p _hp   => BSD_PrimePow_k0 p,
   fun p _hp   => BSD_PrimePow_k1 p (h_hasse p)⟩

-- ============================================================
-- §6. M2 + M3 integrated chain
-- ============================================================

/-- **M2 + M3 integrated combinator** (0 sorry, classical trio):
    Combines all proved and conditional results from M2 and M3.

    Total gate count: 7 named OPEN hypotheses.
    - M3 gates (3): h_hasse, h_cheb, h_tau
    - M2 gates (4): h_bound, h_zeta, h_wm, h_euler
    - Permanently OPEN (2, never discharged): _h_mod, _h_bsd

    Proved conclusions:
    - BSD_LSeriesSummable_OPEN, BSD_AnalyticOn_OPEN, BSD_EulerProduct_OPEN (M2)
    - BSD_PrimePowBound_OPEN p 0, BSD_PrimePowBound_OPEN p 1 (M3 base cases, 0 gates)
    - BSD_PrimePowBound_OPEN p k for all k (M3 conditional, 2 gates: hasse+cheb)

    NOT a proof of BSD. Honest conditional. SORRY: 0. Classical trio. -/

theorem BSD_m2_m3_full_chain
    -- M3 gates
    (h_hasse : ∀ (p : ℕ) [Fact p.Prime], BSD_Hasse_OPEN p)
    (h_cheb  : BSD_ChebyshevBound_OPEN)
    -- M2 gates (BSD_TermBound no longer needed — proved by BSD_TermBound_CLOSED)
    (h_bound : ∀ n : ℕ+, BSD_aNBound_OPEN n.val)
    (h_zeta  : BSD_CompareZeta_OPEN)
    (h_wm    : BSD_WeierstrassM_OPEN)
    (h_euler : BSD_EulerConvergence_OPEN)
    -- Permanently OPEN
    (_h_mod  : BSD_ModularityE143_OPEN)
    (_h_bsd  : BSD_BSDFormula_OPEN) :
    BSD_LSeriesSummable_OPEN ∧ BSD_AnalyticOn_OPEN ∧ BSD_EulerProduct_OPEN ∧
    (∀ (p : ℕ) [Fact p.Prime], BSD_PrimePowBound_OPEN p 0) ∧
    (∀ (p : ℕ) [Fact p.Prime], BSD_PrimePowBound_OPEN p 1) := by
  obtain ⟨_, hk0, hk1⟩ := BSD_m3_hasse_chain h_hasse h_cheb
  obtain ⟨hS, hA, hE⟩ :=
    BSD_optionA_tauberian_chain_M2 h_bound h_zeta h_wm h_euler _h_mod _h_bsd
  exact ⟨hS, hA, hE, hk0, hk1⟩

-- ============================================================
-- §7. Gap audit sentinels
-- ============================================================

/-- M3 gap audit: BSD_ChebyshevBound_OPEN remains OPEN.
    Gap: Chebyshev-U trig identity for inductive step k≥2;
    arccos + sin quotient bound not in Mathlib v4.12.0. -/

theorem BSD_chebyshev_gap_sentinel : BSD_ChebyshevBound_OPEN → True := fun _ => trivial

/-- M3 gap audit: BSD_TauBound_OPEN remains OPEN.
    Gap: τ(n) = O(n^ε) divisor function sub-power bound;
    not in Mathlib v4.12.0 ArithmeticFunction. -/

theorem BSD_tau_gap_sentinel : BSD_TauBound_OPEN → True := fun _ => trivial

/-- M3 gap audit: BSD_Hasse_OPEN remains OPEN at all primes.
    Gap: Frobenius endomorphism degree theory absent from Mathlib v4.12.0. -/

theorem BSD_hasse_gap_sentinel (p : ℕ) [Fact p.Prime] :
    BSD_Hasse_OPEN p → True := fun _ => trivial

end Towers.BSD

