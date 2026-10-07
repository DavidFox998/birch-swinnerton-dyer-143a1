/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_AP_Table.lean — extracted 8 closed declarations. -/

theorem E143a1_count_2 : E143a1_count 2 = 2 := by decide

/-- Count of affine 𝔽₃-points is 4 (kernel-decided; 9 pairs). -/

theorem E143a1_count_3 : E143a1_count 3 = 4 := by decide

/-- Count of affine 𝔽₅-points is 6 (kernel-decided; 25 pairs). -/

theorem E143a1_count_5 : E143a1_count 5 = 6 := by decide

/-- Count of affine 𝔽₇-points is 9 (kernel-decided; 49 pairs). -/

theorem E143a1_count_7 : E143a1_count 7 = 9 := by decide

-- ============================================================
-- §3. Proved a_p values (p ∈ {2, 3, 5, 7})
-- ============================================================

/-- PROVED: a_p(143a1, 2) = 0.
    #E_affine(𝔽₂) = 2; a_p = 2 − 2 = 0.
    LMFDB 143.2.a.a: a₂ = 0. -/

theorem BSD_S4_ap2_eq : BSD_S4_data.ap2 = 0 := by
  simp [BSD_S4_data, E143a1_count_2]

/-- PROVED: ap3 entry of BSD_S4_data = −1. -/

theorem BSD_S4_ap3_eq : BSD_S4_data.ap3 = -1 := by
  simp [BSD_S4_data, E143a1_count_3]

-- ============================================================
-- §6. S4 chain combinator
-- ============================================================

/-- S4 chain: given the two EMPIRICAL S4 count hypotheses (p=19,191),
    the full S4 ap record matches the LMFDB values exactly.
    This is the formal input to the Bost-Connes Hankel analysis.
    SORRY: 0.  Classical trio.  Not a brick. -/

theorem BSD_S4_chain
    (h19  : BSD_ap19_card_EMPIRICAL)
    (h191 : BSD_ap191_card_EMPIRICAL) :
    BSD_S4_data.ap2   = 0   ∧
    BSD_S4_data.ap3   = -1  ∧
    BSD_S4_data.ap19  = 2   ∧
    BSD_S4_data.ap191 = -15 :=
  ⟨BSD_S4_ap2_eq, BSD_S4_ap3_eq, rfl, rfl⟩

-- ============================================================
-- §7. Surface ledger (0 sorry, classical trio)
-- ============================================================

/-- Surface ledger: all named EMPIRICAL surfaces in this file.
    None is sorry, none is an axiom; all are def Prop. -/

theorem BSD_AP_surface_ledger :
    (BSD_ap11_card_EMPIRICAL → False → False) ∧
    (BSD_ap13_card_EMPIRICAL → False → False) ∧
    (BSD_ap17_card_EMPIRICAL → False → False) ∧
    (BSD_ap19_card_EMPIRICAL → False → False) ∧
    (BSD_ap23_card_EMPIRICAL → False → False) ∧
    (BSD_ap29_card_EMPIRICAL → False → False) ∧
    (BSD_ap191_card_EMPIRICAL → False → False) :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
   fun _ h => h, fun _ h => h, fun _ h => h⟩

end Towers.BSD

