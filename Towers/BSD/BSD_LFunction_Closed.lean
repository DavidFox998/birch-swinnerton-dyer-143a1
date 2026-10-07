/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_LFunction_Closed.lean — extracted 12 closed declarations. -/

theorem BSD_TermBound_CLOSED : BSD_TermBound_OPEN := by
  intro n s h_bound
  have hn_pos : (0 : ℝ) < (n.val : ℝ) := by exact_mod_cast n.pos
  -- Rewrite LHS: split norm over division
  rw [norm_div]
  -- Numerator: cast a_n n.val : ℤ through ℝ to use Complex.norm_real
  have h_num : ‖(a_n n.val : ℂ)‖ = |(a_n n.val : ℝ)| := by
    have : (a_n n.val : ℂ) = ((a_n n.val : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  -- Denominator: ‖(↑r : ℂ)^s‖ = r^s.re for positive real r
  have h_den : ‖(n : ℂ) ^ s‖ = (n.val : ℝ) ^ s.re := by
    have : (n : ℂ) = ((n.val : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos hn_pos]
  -- Reassemble and apply the coefficient bound
  rw [h_num, h_den]
  exact (div_le_div_right (Real.rpow_pos_of_pos hn_pos _)).mpr h_bound

-- ============================================================
-- §3. Milestone 1 conditional closure theorems (unchanged)
-- ============================================================

/-!
### Conditional closure 1: BSD_LSeriesSummable (Milestone 1)

Given BSD_TermBound_OPEN (now proved) + BSD_CompareZeta_OPEN,
the Dirichlet series converges absolutely for Re(s) > 3/2.
-/

/-- **CONDITIONAL M1** (0 sorry): given `BSD_aNBound_OPEN` (∀ n) + `BSD_TermBound_OPEN` +
    `BSD_CompareZeta_OPEN`, the Dirichlet series L(E₁₄₃, s) = ∑ a_n/n^s is absolutely
    convergent for Re(s) > 3/2.

    Proof: Summable.of_norm_bounded against the √n·τ(n)/n^σ majorant. -/

theorem BSD_LSeriesSummable_CLOSED
    (h_bound : ∀ n : ℕ+, BSD_aNBound_OPEN n.val)
    (h_term  : BSD_TermBound_OPEN)
    (h_zeta  : BSD_CompareZeta_OPEN) :
    BSD_LSeriesSummable_OPEN :=
  fun s hs =>
    Summable.of_norm_bounded
      (fun n : ℕ+ => Real.sqrt (n.val : ℝ) * (n.val.divisors.card : ℝ) / (n.val : ℝ) ^ s.re)
      (h_zeta s.re hs)
      (fun n => h_term n s (h_bound n))

/-!
### Milestone 2 strengthening: BSD_LSeriesSummable_CLOSED_M2

Now that BSD_TermBound_CLOSED is proved, the hypothesis `BSD_TermBound_OPEN` can be
dropped from the gate condition.  The gate count drops from 3 to 2.
-/

/-- **M2 STRENGTHENED** (0 sorry, classical trio): given only `BSD_aNBound_OPEN` (∀ n)
    + `BSD_CompareZeta_OPEN`, the Dirichlet series L(E₁₄₃, s) converges absolutely
    for Re(s) > 3/2.

    Improvement over M1: `BSD_TermBound_OPEN` is no longer a hypothesis — it is
    discharged internally by `BSD_TermBound_CLOSED`. -/

theorem BSD_LSeriesSummable_CLOSED_M2
    (h_bound : ∀ n : ℕ+, BSD_aNBound_OPEN n.val)
    (h_zeta  : BSD_CompareZeta_OPEN) :
    BSD_LSeriesSummable_OPEN :=
  BSD_LSeriesSummable_CLOSED h_bound BSD_TermBound_CLOSED h_zeta

/-!
### Conditional closure 2: BSD_AnalyticOn (Milestone 1, unchanged)
-/

/-- **CONDITIONAL M1** (0 sorry): given `BSD_LSeriesSummable_OPEN` + `BSD_WeierstrassM_OPEN`,
    L(E₁₄₃, s) is analytic on {s : ℂ | Re(s) > 3/2}. -/

theorem BSD_AnalyticOn_CLOSED
    (h_summ : BSD_LSeriesSummable_OPEN)
    (h_wm   : BSD_WeierstrassM_OPEN) :
    BSD_AnalyticOn_OPEN :=
  h_wm h_summ

/-!
### Conditional closure 3: BSD_EulerProduct (Milestone 1, unchanged)
-/

/-- **CONDITIONAL M1** (0 sorry): given `BSD_LSeriesSummable_OPEN` + `BSD_EulerConvergence_OPEN`,
    the Euler product identity holds for Re(s) > 3/2. -/

theorem BSD_EulerProduct_CLOSED
    (h_summ  : BSD_LSeriesSummable_OPEN)
    (h_euler : BSD_EulerConvergence_OPEN) :
    BSD_EulerProduct_OPEN :=
  h_euler h_summ

-- ============================================================
-- §4. Status: permanently OPEN surfaces
-- ============================================================

/-- Documentation: `BSD_ModularityE143_OPEN` is permanently OPEN in this tower.
    Wiles–Taylor theorem (E/ℚ is modular) is not formalized in Mathlib v4.12.0.
    This sentinel records that fact explicitly. -/

theorem BSD_modularityE143_is_open : BSD_ModularityE143_OPEN → BSD_ModularityE143_OPEN :=
  id

/-- Documentation: `BSD_BSDFormula_OPEN` is permanently OPEN in this tower.
    It IS the Birch and Swinnerton-Dyer conjecture (rank = analytic rank).
    This sentinel records that fact explicitly. -/

theorem BSD_bsdFormula_is_open : BSD_BSDFormula_OPEN → BSD_BSDFormula_OPEN :=
  id

-- ============================================================
-- §5. M2 audit: remaining OPEN sub-surfaces and their gaps
-- ============================================================

/-!
### Milestone 2 honest audit

Three sub-surfaces remain OPEN after M2.  Their gaps are documented here.
-/

/-- M2 audit — BSD_CompareZeta_OPEN remains OPEN.
    Elementary bound: τ(n) ≤ n ⟹ ∑ √n·τ(n)/n^σ ≤ ∑ 1/n^(σ-3/2), summable only for σ>5/2.
    Closing at σ>3/2 requires τ(n)=O(n^ε) or ∑τ(n)/n^s = ζ(s)²; neither in Mathlib v4.12.0.
    This sentinel names the gap without discharging it. -/

theorem BSD_compareZeta_gap_sentinel :
    (∀ (n : ℕ+), BSD_CompareZeta_OPEN → True) := fun _ _ => trivial

/-- M2 audit — BSD_WeierstrassM_OPEN remains OPEN.
    Gap: `BSD_LSeriesSummable_OPEN` gives only pointwise summability; analyticity requires
    locally uniform convergence (normal convergence on compacts).  Mathlib v4.12.0 has
    `analyticOn_tsum` but it requires the locally-normal condition, not just pointwise. -/

theorem BSD_weierstrassM_gap_sentinel :
    (BSD_WeierstrassM_OPEN → True) := fun _ => trivial

/-- M2 audit — BSD_EulerConvergence_OPEN remains OPEN.
    Gap: Euler product theorem for multiplicative arithmetic functions is absent from
    Mathlib v4.12.0.  Two sub-gaps: (a) local factor identity via Hecke recurrence geometric
    series; (b) product convergence theorem.  Neither is an easy Lean proof. -/

theorem BSD_eulerConvergence_gap_sentinel :
    (BSD_EulerConvergence_OPEN → True) := fun _ => trivial

-- ============================================================
-- §6. Option A chain combinators
-- ============================================================

/-- **Milestone 1 chain** (0 sorry, classical trio):
    Given all four sub-surface hypotheses, closes BSD_LSeriesSummable, BSD_AnalyticOn,
    and BSD_EulerProduct, and names the two permanently OPEN gaps.

    Kept for backward compatibility.  See `BSD_optionA_tauberian_chain_M2` for the
    Milestone 2 strengthening (one fewer hypothesis). -/

theorem BSD_optionA_tauberian_chain
    (h_bound : ∀ n : ℕ+, BSD_aNBound_OPEN n.val)
    (h_term  : BSD_TermBound_OPEN)
    (h_zeta  : BSD_CompareZeta_OPEN)
    (h_wm    : BSD_WeierstrassM_OPEN)
    (h_euler : BSD_EulerConvergence_OPEN)
    -- Permanently OPEN gaps (named explicitly, never discharged here)
    (_h_mod  : BSD_ModularityE143_OPEN)
    (_h_bsd  : BSD_BSDFormula_OPEN) :
    BSD_LSeriesSummable_OPEN ∧ BSD_AnalyticOn_OPEN ∧ BSD_EulerProduct_OPEN := by
  have hS := BSD_LSeriesSummable_CLOSED h_bound h_term h_zeta
  exact ⟨hS, BSD_AnalyticOn_CLOSED hS h_wm, BSD_EulerProduct_CLOSED hS h_euler⟩

/-- **Milestone 2 chain** (0 sorry, classical trio):
    Strengthening of `BSD_optionA_tauberian_chain` — drops `BSD_TermBound_OPEN` as a
    hypothesis since `BSD_TermBound_CLOSED` now discharges it internally.

    Gate count: 5 hypotheses (was 6).  The one proved gap: BSD_TermBound.
    Three remaining gates: BSD_aNBound_OPEN (∀n), BSD_CompareZeta_OPEN,
    BSD_WeierstrassM_OPEN, BSD_EulerConvergence_OPEN.

    NOT a proof of BSD.  NOT a proof of modularity.
    This is the honest conditional chain for the analytic route after M2. -/

theorem BSD_optionA_tauberian_chain_M2
    (h_bound : ∀ n : ℕ+, BSD_aNBound_OPEN n.val)
    (h_zeta  : BSD_CompareZeta_OPEN)
    (h_wm    : BSD_WeierstrassM_OPEN)
    (h_euler : BSD_EulerConvergence_OPEN)
    -- Permanently OPEN gaps (named explicitly, never discharged here)
    (_h_mod  : BSD_ModularityE143_OPEN)
    (_h_bsd  : BSD_BSDFormula_OPEN) :
    BSD_LSeriesSummable_OPEN ∧ BSD_AnalyticOn_OPEN ∧ BSD_EulerProduct_OPEN := by
  have hS := BSD_LSeriesSummable_CLOSED_M2 h_bound h_zeta
  exact ⟨hS, BSD_AnalyticOn_CLOSED hS h_wm, BSD_EulerProduct_CLOSED hS h_euler⟩

end Towers.BSD

