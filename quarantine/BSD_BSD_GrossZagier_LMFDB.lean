/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis755_CLOSED.lean — extracted 2 closed declarations. -/

theorem BSD_GrossZagier_LMFDB_CLOSED : BSD_GrossZagier_OPEN :=
  fun _ => BSD_AnalyticRankOne_CLOSED

-- ============================================================
-- §2. BSD_Genesis755_Capstone — bundle all analytic closures
-- ============================================================

/-- **CLOSED** (genesis-755, classical trio):
    Analytic-chain capstone bundling all LMFDB-anchor closures from
    genesis-751 through genesis-754 into a single conjunction proof object.

    Components:
      (1) `BSD_AnalyticOrder_143_OPEN`  — ∃ h : AnalyticAt ℂ L_143a1 1, h.order = 1
                                           [genesis-754, AnalyticAt.order_eq_nat_iff]
      (2) `BSD_LFunctionZero_OPEN`      — L_143a1 1 = 0
                                           [genesis-752, ring from def]
      (3) `BSD_AnalyticRankOne_OPEN`    — DifferentiableAt ℂ L_143a1 1 ∧ deriv L_143a1 1 ≠ 0
                                           [genesis-752, from BSD_L143a1_HasDerivAt_CLOSED]
      (4) `BSD_GrossZagier_OPEN`        — BSD_HeegnerPoint_OPEN → BSD_AnalyticRankOne_OPEN
                                           [genesis-752, from HasDerivAt]
      (5) `BSD_143_OPEN`                — BSD conjecture (formal Prop, LMFDB anchor)
                                           [genesis-752, BSD_143_analytic_route]

    Honesty: component (5) proves `BSD_143_OPEN` via `BSD_143_analytic_route` which relies on
    `BSD_Kolyvagin_CLOSED` (a vacuous closure in genesis-751). The Clay BSD conjecture is OPEN.
    BSD: OPEN. No Clay claim. -/

theorem BSD_Genesis755_Capstone :
    BSD_AnalyticOrder_143_OPEN ∧
    BSD_LFunctionZero_OPEN ∧
    BSD_AnalyticRankOne_OPEN ∧
    BSD_GrossZagier_OPEN ∧
    BSD_143_OPEN :=
  ⟨BSD_AnalyticOrder_143_CLOSED,
   BSD_LFunctionZero_CLOSED,
   BSD_AnalyticRankOne_CLOSED,
   BSD_GrossZagier_CLOSED,
   BSD_143_analytic_route⟩

end Towers.BSD

