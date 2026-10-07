/- Ported closed theorems from birch-swinnerton-dyer-143/Genus_X0_143.lean — extracted 2 closed declarations. -/

theorem chi_neg4_13 : ((-4 : ZMod 13) ^ ((13 - 1) / 2) : ZMod 13) = 1 := by decide

/-- χ₋₃(11) = (−3/11) = −1.
    Verified: (−3 mod 11) = 8; 8^5 mod 11 = 10 ≡ −1 mod 11. -/

theorem chi_neg3_13 : ((-3 : ZMod 13) ^ ((13 - 1) / 2) : ZMod 13) = 1 := by decide

/-! ## §2. Index and cusp-count arithmetic -/

/-- μ = 143 × (12/11) × (14/13) = 168 (integer arithmetic). -/

