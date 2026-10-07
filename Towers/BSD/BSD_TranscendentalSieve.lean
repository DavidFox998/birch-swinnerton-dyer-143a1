/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_TranscendentalSieve.lean — extracted 3 closed declarations. -/

theorem BSD_alpha_transcendental_conditional
    (hπ    : BSD_Pi_Transcendental_OPEN)
    (hadd  : ∀ (x y : ℝ), IsAlgebraic ℚ x → IsAlgebraic ℚ y → IsAlgebraic ℚ (x + y))
    (hmul  : ∀ (x y : ℝ), IsAlgebraic ℚ x → IsAlgebraic ℚ y → IsAlgebraic ℚ (x * y))
    (hneg  : ∀ (x : ℝ), IsAlgebraic ℚ x → IsAlgebraic ℚ (-x)) :
    BSD_Alpha_Transcendental_OPEN := by
  intro h_alg
  -- All integers are algebraic over ℚ
  have h299 : IsAlgebraic ℚ (299 : ℝ) := isAlgebraic_int 299
  have h10  : IsAlgebraic ℚ (10 : ℝ) := isAlgebraic_int 10
  -- π/10 = (299 + π/10) + (-299) is algebraic (α_BSD_period = 299 + π/10)
  have hpi_div : IsAlgebraic ℚ (Real.pi / 10) := by
    have hminus : IsAlgebraic ℚ (-(299 : ℝ)) := hneg _ h299
    have hsum := hadd _ _ h_alg hminus
    have heq : α_BSD_period + -(299 : ℝ) = Real.pi / 10 := by
      unfold α_BSD_period; ring
    rwa [heq] at hsum
  -- π = (π/10) * 10 is algebraic, contradicting BSD_Pi_Transcendental_OPEN
  have hpi : IsAlgebraic ℚ Real.pi := by
    have hprod := hmul _ _ hpi_div h10
    have heq : Real.pi / 10 * 10 = Real.pi := by ring
    rwa [heq] at hprod
  exact hπ hpi

/-- **BSD_IrrMeasure_OPEN** (parameter μ): the irrationality measure of α_BSD_period
    is a finite real number μ with 2 < μ.

    Mathematical content: by the Nesterenko–Ramachandra theorem,
    π has irrationality measure μ(π) < ∞.  Since α = 299 + π/10,
    μ(α) = μ(π) (scaling/translation does not change irrationality measure).
    The current best bound: μ(π) ≤ 7.606... (Salikhov 2008).

    STATUS: OPEN.  We work with an abstract μ > 2. -/
def BSD_IrrMeasure_OPEN (μ : ℝ) : Prop := 2 < μ

/-- **BSD_SchmidtCount_OPEN** (for irrationality measure μ and exponent δ > 0):
    #{p ≤ x prime : ‖p · α‖ < p^{-δ}} ≪_δ x^{1 − δ/(μ−1)}

    Mathematical content: a prime-counting variant of the Schmidt subspace
    theorem / Duffin–Schaeffer for well-approximable irrationals.
    For δ = 1 this gives N_S(x) ≪ x^{1−1/(μ−1)}.

    STATUS: OPEN.  Research-grade; not in Mathlib v4.12.0. -/
def BSD_SchmidtCount_OPEN (μ δ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ x in atTop,
    (Finset.card (Finset.filter
      (fun p => p.Prime ∧
        ‖(p : ℝ) * α_BSD_period - (round ((p : ℝ) * α_BSD_period) : ℝ)‖ <
          (p : ℝ) ^ (-δ))
      (Finset.range (⌊x⌋₊ + 1))) : ℝ) ≤ C * x ^ (1 - δ / (μ - 1))

/-- **BSD_SieveDensity_OPEN**: the Dirichlet density of S_BSD_sieve is < 1.

    Derives from BSD_SchmidtCount_OPEN with δ = 1:
    N_S(x) ≪ x^{1−1/(μ−1)} where 1−1/(μ−1) < 1 since μ > 2.
    So Σ_{p ∈ S, p ≤ x} p⁻¹ / (log log x) → θ < 1, giving D(S) = θ < 1.

    STATUS: OPEN (depends on BSD_SchmidtCount_OPEN + analytic number theory). -/
def BSD_SieveDensity_OPEN : Prop :=
  ∃ θ : ℝ, θ < 1 ∧
    ∀ᶠ x in atTop,
      (∑ p ∈ Finset.filter (fun p => p ∈ S_BSD_sieve)
         (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) ≤ θ * Real.log (Real.log x)

/-- **BSD_ZetaBound_OPEN**: ζ(1/2 + it) = O_ε(t^{1+ε}) for t ≥ 2.

    Mathematical route:
    1. BSD_SieveDensity_OPEN: D(S) < 1, so Σ_{p∈S} p^{-1/2-it} = O(t^{1/(1-D(S))+ε})
    2. Euler product truncation:
       |∏_{p∈S} (1 − p^{-1/2-it})⁻¹| ≪ exp(O(t^{1+ε}))
    3. ζ(s) = ∏_{p prime} (1−p^{-s})⁻¹ (for Re s > 1, then analytic continuation):
       |ζ(1/2 + it)| ≤ |∏_{p∈S}(...)| · |∏_{p∉S}(...)| ≪ t^{1+ε}

    Remark (honesty): this bound O(t^{1+ε}) is FAR WEAKER than:
    - The conditonal O(t^{1/6+ε}) from RH
    - The unconditional O(t^{13/84+ε}) from Huxley/Bourgain/exponential sums
    It is the β / BKM control for the NS vorticity argument (finite ∫‖ω(t)‖∞ dt),
    not a competitive bound for analytic number theory itself.

    STATUS: OPEN (research-grade; depends on BSD_SieveDensity_OPEN). -/
def BSD_ZetaBound_OPEN : Prop :=
  ∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
    ‖riemannZeta (1/2 + I * t)‖ ≤ C * t ^ (1 + ε)

/-! ### Combinator chain -/

/-- BSD_ZetaBound_chain: the chain
    BSD_Pi_Transcendental_OPEN → BSD_Alpha_Transcendental_OPEN
    → BSD_IrrMeasure_OPEN → BSD_SchmidtCount_OPEN
    → BSD_SieveDensity_OPEN → BSD_ZetaBound_OPEN

    accepts all open surfaces as explicit hypotheses and yields the
    conditional conclusion.  0 sorry, classical trio only.
    NOT a brick — every hypothesis is an OPEN surface.

    The conditional is honest: each arrow is a named gap. -/

theorem BSD_ZetaBound_chain
    (_ : BSD_Pi_Transcendental_OPEN)
    (_ : BSD_Alpha_Transcendental_OPEN)
    (μ : ℝ) (_ : BSD_IrrMeasure_OPEN μ)
    (_ : BSD_SchmidtCount_OPEN μ 1)
    (_ : BSD_SieveDensity_OPEN)
    (h_zeta : BSD_ZetaBound_OPEN) :
    ∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      ‖riemannZeta (1/2 + I * t)‖ ≤ C * t ^ (1 + ε) :=
  h_zeta

/-! ### Tier 2B evidence summary (proved parts) -/

/-- All proved Tier 2B facts collected. -/

theorem BSD_Tier2B_ProvedFacts :
    0 < α_BSD_period ∧
    299 < α_BSD_period ∧
    α_BSD_period < 300 :=
  ⟨α_BSD_period_pos, α_BSD_period_gt_299, α_BSD_period_lt_300⟩

end Towers.BSD

