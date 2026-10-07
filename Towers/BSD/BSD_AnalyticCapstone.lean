/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_AnalyticCapstone.lean — extracted 8 closed declarations. -/

theorem BSD_L143a1_DerivAtOne_Nonzero : BSD_L143a1_DerivAtOne ≠ 0 := by
  simp only [BSD_L143a1_DerivAtOne]
  norm_num

/-- **CLOSED** (norm_num): BSD_LeadingCoeff 143 ≠ 0.
    37006603 / 25000000 ≠ 0 — the leading coefficient L*(143a1, 1) = Ω · R · ∏cₚ is nonzero.
    Encodes: 1.2583 · 0.5882 · 2 = 1.4804... > 0 (all factors positive, LMFDB). -/

theorem BSD_LeadingCoeff_Nonzero_CLOSED : BSD_LeadingCoeff 143 ≠ 0 := by
  simp only [BSD_LeadingCoeff]
  norm_num

/-- **CLOSED** (norm_num): VanishingOrder LMFDB anchor at N = 143 equals 1. -/

theorem BSD_VanishingOrderAnchor_eq_one :
    BSD_VanishingOrderAnchor 143 = 1 := by
  simp [BSD_VanishingOrderAnchor]

/-- **CLOSED** (norm_num): VanishingOrder anchor = AnalyticRankAnchor at N = 143.
    Both encode the same LMFDB datum: analytic rank of 143a1 is 1. -/

theorem BSD_VanishingOrderAnchor_eq_AnalyticRankAnchor :
    BSD_VanishingOrderAnchor 143 = BSD_AnalyticRankAnchor 143 := by
  simp [BSD_VanishingOrderAnchor, BSD_AnalyticRankAnchor]

-- ============================================================
-- §3. Precise OPEN surfaces in Mathlib API types
-- ============================================================

/-- **OPEN — HasDerivAt LMFDB anchor surface** (genesis-750):
    L_143a1 has complex derivative (5759/10000 : ℂ) at s = 1.

    Mathematical content: L'(143a1, 1) ≈ 0.5759... ≠ 0 (LMFDB 143.2.a.a; analytic rank 1,
    simple zero). This is the **analytic observation** that closes `BSD_AnalyticRankOne_OPEN`
    when combined with Mathlib's `HasDerivAt.differentiableAt` and `HasDerivAt.deriv`.

    Closure path (not achievable without the following steps):
      1. Identify L_143a1 with the actual Hasse-Weil Euler product (BSD_LFunction_ID_OPEN)
      2. Prove analytic continuation via Wiles-Taylor modularity (~6-12 months Lean work)
      3. Prove L'(1) ≠ 0 via certified GMP-backed numerics with error bounds

    STATUS: OPEN. -/
def BSD_L143a1_HasDerivAt_OPEN : Prop :=
  HasDerivAt L_143a1 BSD_L143a1_DerivAtOne 1

/-- **OPEN — Mathlib AnalyticAt.order surface** (genesis-750):
    L_143a1 is analytic at s = 1 with Mathlib order of vanishing equal to 1.

    Uses Mathlib's `AnalyticAt.order : ℕ∞` (from Mathlib.Analysis.Analytic.IsolatedZeros).
    `AnalyticAt.order_eq_nat_iff` characterizes order = n in terms of Taylor coefficients.
    This is the precise Mathlib-API version of `BSD_VanishingOrder_143_Genuine_OPEN`.

    Separated from `BSD_VanishingOrder_143_Genuine_OPEN` because `VanishingOrder` (B01
    opaque) has no proved connection to `AnalyticAt.order` (see BSD_VanishingOrder_APIBridge_OPEN).

    STATUS: OPEN. -/
def BSD_AnalyticOrder_143_OPEN : Prop :=
  ∃ h : AnalyticAt ℂ L_143a1 1, h.order = (1 : ℕ∞)

/-- **OPEN — VanishingOrder ↔ AnalyticAt.order API bridge surface** (genesis-750):
    The opaque `VanishingOrder` (B01, `noncomputable opaque VanishingOrder : (ℂ→ℂ)→ℂ→ℕ`)
    equals the Mathlib `AnalyticAt.order` cast to ℕ∞.

    This surface is the **single API gap** separating the B01 formulation of the analytic rank
    from Mathlib's formulation. If `VanishingOrder` were redefined as `fun f s =>
    (h : AnalyticAt ℂ f s).order.toNat` (with `h` provided by analytic continuation),
    this would hold by definition. The gap is that B01's opaque constant has no
    definitional reduction.

    STATUS: OPEN. -/
def BSD_VanishingOrder_APIBridge_OPEN : Prop :=
  ∀ (f : ℂ → ℂ) (s : ℂ) (h : AnalyticAt ℂ f s),
    (VanishingOrder f s : ℕ∞) = h.order

/-- **OPEN — L-function opaque equality surface** (genesis-750):
    The opaque constant `L_143a1` (BSD_AnalyticRank.lean §0) equals `BSDLFunction 143`
    (B01_EllipticCurve.lean). Both are classical-trio-honest opaque anchors for the same
    Hecke L-function; they are defined independently and their equality is not provable
    without this bridge surface.

    Note: `BSD_LFunction_Identification_OPEN` (B02_Modularity_Closed.lean) is a DIFFERENT
    surface: it identifies BSDLFunction 143 with the Dirichlet series on {Re s > 3/2}.
    This surface bridges the TWO opaque constants: `L_143a1` ↔ `BSDLFunction 143`.

    Closure path: explicit connection of both opaque constants to the same Euler product.

    STATUS: OPEN. -/
def BSD_L143a1_BSDLFunction_ID_OPEN : Prop :=
  L_143a1 = BSDLFunction 143

-- ============================================================
-- §4. Conditional closures (0 sorry, classical trio)
-- ============================================================

/-- **CLOSED conditional** (0 sorry, classical trio):
    Given the HasDerivAt LMFDB anchor, close `BSD_AnalyticRankOne_OPEN`.

    BSD_AnalyticRankOne_OPEN = DifferentiableAt ℂ L_143a1 1 ∧ deriv L_143a1 1 ≠ 0.

    Proof via pure Mathlib API:
      h.differentiableAt : HasDerivAt → DifferentiableAt ℂ L_143a1 1     (Mathlib)
      h.deriv            : HasDerivAt → deriv L_143a1 1 = BSD_L143a1_DerivAtOne  (Mathlib)
      BSD_L143a1_DerivAtOne_Nonzero : (5759/10000 : ℂ) ≠ 0               (norm_num)

    Note: this is LMFDB-level, not Clay-level — `h` is an OPEN surface, not a theorem. -/

theorem BSD_AnalyticRankOne_from_HasDerivAt
    (h : BSD_L143a1_HasDerivAt_OPEN) :
    BSD_AnalyticRankOne_OPEN := by
  constructor
  · exact h.differentiableAt
  · rw [h.deriv]
    exact BSD_L143a1_DerivAtOne_Nonzero

/-- **CLOSED conditional** (0 sorry, classical trio):
    Given the HasDerivAt LMFDB anchor, close `BSD_GrossZagier_OPEN`.

    BSD_GrossZagier_OPEN = BSD_HeegnerPoint_OPEN → BSD_AnalyticRankOne_OPEN.
    With BSD_AnalyticRankOne_OPEN established by the anchor, the Heegner hypothesis
    is unused — the closure is via NUMERICAL non-vanishing of L'(1), not via the
    Gross-Zagier height formula.

    **Honest note**: this is NOT a proof of Gross-Zagier (1986). The GZ theorem says
    L'(1) ≠ 0 ↔ ĥ(y_K) > 0. Here we bypass GZ entirely: L'(1) ≠ 0 is an analytic
    observation (LMFDB anchor), not derived from the Heegner height. -/

theorem BSD_GrossZagier_from_HasDerivAt
    (h : BSD_L143a1_HasDerivAt_OPEN) :
    BSD_GrossZagier_OPEN :=
  fun _ => BSD_AnalyticRankOne_from_HasDerivAt h

/-- **CLOSED conditional** (0 sorry, classical trio):
    Given 3 API surfaces, close `BSD_VanishingOrder_143_Genuine_OPEN`.

    VanishingOrder (BSDLFunction 143) 1 = 1.

    Chain:
      h_id  : L_143a1 = BSDLFunction 143  (identification)
      h_api : (VanishingOrder f s : ℕ∞) = (analyticAt f s).order  (API bridge)
      h_ord : ∃ ha : AnalyticAt ℂ L_143a1 1, ha.order = 1         (AnalyticAt.order)
    → VanishingOrder (BSDLFunction 143) 1 = 1.

    Note: all 3 hypotheses are OPEN surfaces; this is a conditional proof. -/

theorem BSD_VanishingOrder_from_API
    (h_id  : BSD_L143a1_BSDLFunction_ID_OPEN)
    (h_api : BSD_VanishingOrder_APIBridge_OPEN)
    (h_ord : BSD_AnalyticOrder_143_OPEN) :
    BSD_VanishingOrder_143_Genuine_OPEN := by
  unfold BSD_VanishingOrder_143_Genuine_OPEN
  obtain ⟨ha, horder⟩ := h_ord
  rw [← h_id]
  exact_mod_cast (h_api L_143a1 1 ha).trans horder

/-- **Clay capstone — analytic-LMFDB route** (0 sorry, classical trio):
    Given 2 surfaces, derive BSD_143_OPEN.

    Required surfaces:
      1. `BSD_L143a1_HasDerivAt_OPEN` — LMFDB anchor: HasDerivAt L_143a1 (5759/10000) 1
      2. `BSD_Kolyvagin_OPEN`         — Euler system: BSD_AnalyticRankOne_OPEN → ∃r=1

    Full chain:
      BSD_AnalyticRankOne_from_HasDerivAt h_hd : BSD_AnalyticRankOne_OPEN
      h_kol (...)                               : ∃ r : ℕ, r = 1
      BSD_RankOneToConj_CLOSED (...)            : BSD_143_OPEN

    **Gap count comparison (routes to BSD_143_OPEN)**:
      genesis-748 (LMFDB):           0 gaps (both anchors = 1 by def)
      genesis-749 (Kolyvagin):       2 gaps (GrossZagier + Kolyvagin)
      genesis-750 (analytic-LMFDB):  2 gaps (HasDerivAt + Kolyvagin)

    **Genuine Clay barrier**: BSD_L143a1_HasDerivAt_OPEN is LMFDB-level, not Clay-level.
    A Clay proof requires HasDerivAt to be derived from axioms, not anchored. -/

theorem BSD_Clay_AnalyticCapstone
    (h_hd  : BSD_L143a1_HasDerivAt_OPEN)
    (h_kol : BSD_Kolyvagin_OPEN) :
    BSD_143_OPEN :=
  BSD_RankOneToConj_CLOSED
    (h_kol (BSD_AnalyticRankOne_from_HasDerivAt h_hd))

-- ============================================================
-- §5. Ledger
-- ============================================================

/-- **BSD_AnalyticCapstone_gap_count** (genesis-750 analytic-LMFDB route): **2**.

    Minimum gap count for BSD_143_OPEN via the analytic-LMFDB route:
      1. BSD_L143a1_HasDerivAt_OPEN   — LMFDB: L'(1) = 5759/10000 ≠ 0
      2. BSD_Kolyvagin_OPEN           — Kolyvagin 1988: Euler systems

    Gap count for BSD_VanishingOrder_143_Genuine_OPEN (genuine Clay level):
      3 sub-gaps (BSD_L143a1_BSDLFunction_ID_OPEN + BSD_VanishingOrder_APIBridge_OPEN
                  + BSD_AnalyticOrder_143_OPEN) — all require Mathlib API absent from v4.12.0.

    BSD: OPEN (Clay). Classical trio. No Clay claim. -/
def BSD_AnalyticCapstone_gap_count : ℕ := 2

end Towers.BSD

