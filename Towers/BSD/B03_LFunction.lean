/- Ported closed theorems from birch-swinnerton-dyer-143/B03_LFunction.lean — extracted 2 closed declarations. -/

theorem B03_BSD_Scaffold
    (h_mod : Modularity_143_OPEN)
    (h_hecke : BSD_L_Analytic_143_OPEN)
    (h_bsd : BSD_143_OPEN)
    (h_tam : BSD_TamagawaConj_OPEN 143)
    (h_reg : BSD_Regulator_OPEN 143)
    (h_sha : BSD_Sha_OPEN 143) :
    BSD_143_OPEN :=
  h_bsd

/-- **BSD_Arithmetic_143_cert** (PROVED, 0 sorry):
    The conductor of E_BSD 143 is 143 = 11 × 13. -/

theorem BSD_Arithmetic_143_cert : (143 : ℕ) = 11 * 13 ∧ (E_BSD 143).conductor = 143 :=
  ⟨by norm_num, BSD_Conductor_143⟩

end Towers.BSD

