/- Ported closed theorems from birch-swinnerton-dyer-143/B06_BSDCollection.lean — extracted 2 closed declarations. -/

theorem BSD_Conditional
    -- Modularity / L-function opens
    (h_mod : Modularity_143_OPEN)
    (h_hecke : BSD_L_Analytic_143_OPEN)
    (h_bsd : BSD_143_OPEN)
    (h_tam : BSD_TamagawaConj_OPEN 143)
    (h_reg : BSD_Regulator_OPEN 143)
    (h_sha : BSD_Sha_OPEN 143)
    -- Class number opens
    (h_upper : K1_Upper_ClassGroup_BSD)
    (h_lower : K1_Lower_OrderOf_BSD)
    -- Number field open
    (h_finrank : BSD_finrank_CLOSED) :
    -- Proved conclusions
    (E_BSD 143).conductor = 143 ∧
    (143 : ℕ) = 11 * 13 ∧
    NrRealPlaces K = 0 ∧
    (2 / Real.pi * Real.sqrt 143 < 8) ∧
    NumberField.classNumber K = 10 ∧
    BSD_143_OPEN :=
  ⟨BSD_Conductor_143,
   BSD_Arithmetic_143,
   nrRealPlaces_zero_BSD,
   minkowski_lt_eight_BSD,
   BSD_ClassNumber_discharged h_upper h_lower,
   h_bsd⟩

/-! ### Arithmetic ledger (all proved, 0 sorry) -/

/-- **BSD_ArithmeticLedger**: all purely arithmetic certificates for the BSD scaffold. -/

theorem BSD_ArithmeticLedger :
    -- Conductor
    (E_BSD 143).conductor = 143 ∧
    (143 : ℕ) = 11 * 13 ∧
    -- Number field
    NrRealPlaces K = 0 ∧
    (2 / Real.pi * Real.sqrt 143 < 8) ∧
    -- Generator cert
    (-28 : ℤ) ^ 2 + (-28) * 3 + 36 * 3 ^ 2 = 1024 ∧
    -- Splitting
    (∃ x : ZMod 2, x ^ 2 - x + 36 = 0) ∧
    (∃ x : ZMod 3, x ^ 2 - x + 36 = 0) ∧
    (∀ x : ZMod 5, x ^ 2 - x + 36 ≠ 0) ∧
    (∃ x : ZMod 7, x ^ 2 - x + 36 = 0) :=
  ⟨BSD_Conductor_143,
   BSD_Arithmetic_143,
   nrRealPlaces_zero_BSD,
   minkowski_lt_eight_BSD,
   norm_form_gen_1024_BSD,
   prime_2_splits_BSD,
   prime_3_splits_BSD,
   prime_5_inert_BSD,
   prime_7_splits_BSD⟩

end Towers.BSD

