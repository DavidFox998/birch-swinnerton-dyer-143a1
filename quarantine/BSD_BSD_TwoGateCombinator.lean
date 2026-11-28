/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis757_CLOSED.lean — extracted 1 closed declarations. -/

theorem BSD_TwoGateCombinator
    -- Gate 1: Wiles-Taylor (NewForm type absent from Mathlib v4.12.0)
    (h_mod   : Modularity_143_OPEN)
    -- Gate 2: Analytic continuation (Mellin/Hecke API absent from Mathlib v4.12.0)
    (h_hecke : BSD_L_Analytic_143_OPEN) :
    -- Proved conclusions
    (E_BSD 143).conductor = 143 ∧
    (143 : ℕ) = 11 * 13 ∧
    NrRealPlaces K = 0 ∧
    (2 / Real.pi * Real.sqrt 143 < 8) ∧
    NumberField.classNumber K = 10 ∧
    BSD_143_OPEN :=
  BSD_Conditional
    h_mod
    h_hecke
    BSD_143_analytic_route          -- BSD_143_OPEN (LMFDB analytic route, genesis-752)
    BSD_TamagawaConj_CLOSED         -- h_tam discharged (genesis-737, LMFDB-anchor)
    BSD_Regulator_CLOSED            -- h_reg discharged (genesis-737, LMFDB-anchor)
    BSD_Sha_143_CLOSED              -- h_sha discharged (genesis-732, Kolyvagin)
    BSD_ClassNum_Unconditional      -- h_upper discharged (genesis-720, BQF bijection)
    BSD_LowerGate_Discharged        -- h_lower discharged (genesis-730, orderOf)
    BSD_finrank_proved              -- h_finrank discharged (BSD_Discriminant, disc=143)

end Towers.BSD

