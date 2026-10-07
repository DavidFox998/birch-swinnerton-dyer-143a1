/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_LAnalytic_Anchor_CLOSED.lean — extracted 3 closed declarations. -/

theorem BSD_L_Analytic_via_LinFunc
    (h : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_L_Analytic_143_OPEN := by
  show AnalyticOn ℂ (BSDLFunction 143) Set.univ
  rw [h]
  exact BSD_AnalyticOn_L143a1_CLOSED

-- ============================================================
-- §3.  Anchor analyticity — documented witness
-- ============================================================

/-- **`BSD_L143a1_Anchor_Analytic`** (0 sorry, classical trio) — PROVED.

    `AnalyticOn ℂ L_143a1 Set.univ` — the LMFDB anchor function is entire.
    Re-export of `BSD_AnalyticOn_L143a1_CLOSED` (genesis-754) for documentation.
    Proof: L_143a1 s = (5759/10000) * (s − 1) is ℂ-linear, hence analytic everywhere.
    This is the proved half of the BSD_L_Analytic_143_OPEN decomposition. -/

theorem BSD_L143a1_Anchor_Analytic : AnalyticOn ℂ L_143a1 Set.univ :=
  BSD_AnalyticOn_L143a1_CLOSED

-- ============================================================
-- §4.  Gap sentinel
-- ============================================================

/-- Gap sentinel: BSD_LFunctionIsLinFunc_OPEN is OPEN (Hecke/Mellin API absent). -/

theorem BSD_linFunc_sentinel : BSD_LFunctionIsLinFunc_OPEN → True := fun _ => trivial

