/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis756_CLOSED.lean — extracted 1 closed declarations. -/

theorem BSD_FourGateCombinator
    (h_mod   : Modularity_143_OPEN)
    (h_hecke : BSD_L_Analytic_143_OPEN)
    (h_tam   : BSD_TamagawaConj_OPEN 143)
    (h_reg   : BSD_Regulator_OPEN 143) :
    (E_BSD 143).conductor = 143 ∧
    (143 : ℕ) = 11 * 13 ∧
    NrRealPlaces K = 0 ∧
    (2 / Real.pi * Real.sqrt 143 < 8) ∧
    NumberField.classNumber K = 10 ∧
    BSD_143_OPEN :=
  BSD_Conditional
    h_mod
    h_hecke
    BSD_143_analytic_route
    h_tam
    h_reg
    BSD_Sha_143_CLOSED
    BSD_ClassNum_Unconditional
    BSD_LowerGate_Discharged
    BSD_finrank_proved

/-! ### §2. Open surface count after genesis-756 -/

/-- The BSD tower has exactly **4 named OPEN surfaces** after genesis-756 (2026-06-27).

    Discharged since BSD_MasterCombinator (was 9):
      BSD_Sha_OPEN 143          → BSD_Sha_143_CLOSED        (genesis-732, Kolyvagin)
      K1_Lower_OrderOf_BSD      → BSD_LowerGate_Discharged   (orderOf API, unconditional)
      K1_Upper_ClassGroup_BSD   → BSD_ClassNum_Unconditional  (BQF bijection, genesis-720)
      BSD_143_OPEN (LMFDB)      → BSD_143_analytic_route      (genesis-752, analytic route)
      BSD_finrank_CLOSED        → BSD_finrank_proved           (BSD_Discriminant, disc=143)

    Also closed in analytic chain (separate from combinator — BSD_LFunction_Chain.lean):
      BSD_LFunctionZero_OPEN    → BSD_LFunctionZero_CLOSED    (genesis-752)
      BSD_AnalyticRankOne_OPEN  → BSD_AnalyticRankOne_CLOSED  (genesis-752)
      BSD_AnalyticOrder_143_OPEN → BSD_AnalyticOrder_143_CLOSED (genesis-754)

    Remaining OPEN (4 genuine Clay gaps):
      Modularity_143_OPEN      — E_{143} modular (Wiles-Taylor; not in Mathlib v4.12.0)
      BSD_L_Analytic_143_OPEN  — analytic continuation (modular forms API absent)
      BSD_TamagawaConj_OPEN    — Tamagawa leading-term formula (Clay core)
      BSD_Regulator_OPEN 143   — Néron-Tate regulator R(E/ℚ) > 0 (height theory absent)

    All are `def Prop` — NOT axioms, NOT sorry, NOT True-stubs.
    BSD: OPEN.  No Clay claim. -/
def BSD_open_surface_count_756 : ℕ := 4

end Towers.BSD

