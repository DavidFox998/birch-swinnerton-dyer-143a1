/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis739_CLOSED.lean — extracted 12 closed declarations. -/

import Towers.BSD.BSD_LFunction

theorem BSD_E143_card_p71 : (E143_Finset 71).card = 80 := by decide

/-- **`BSD_E143_card_p73`** — 143a1 has exactly **89 affine 𝔽₇₃-points**.
    a₇₃ = 73−89 = −16.  Computed by `decide` over ZMod 73 × ZMod 73 (5329 pairs). -/

theorem BSD_E143_card_p73 : (E143_Finset 73).card = 89 := by decide

/-- **`BSD_E143_card_p79`** — 143a1 has exactly **71 affine 𝔽₇₉-points**.
    a₇₉ = 79−71 = +8.  Computed by `decide` over ZMod 79 × ZMod 79 (6241 pairs). -/

theorem BSD_E143_card_p79 : (E143_Finset 79).card = 71 := by decide

/-! ## §2. Exact a_p values -/

/-- **`BSD_ap_p71`** — `a_p 71 = −9`.  From a_p 71 = 71 − 80. -/

theorem BSD_ap_p71 : a_p 71 = (-9 : ℤ) := by
  have h := BSD_E143_card_p71; unfold a_p; omega

/-- **`BSD_ap_p73`** — `a_p 73 = −16`.  From a_p 73 = 73 − 89. -/

theorem BSD_ap_p73 : a_p 73 = (-16 : ℤ) := by
  have h := BSD_E143_card_p73; unfold a_p; omega

/-- **`BSD_ap_p79`** — `a_p 79 = +8`.  From a_p 79 = 79 − 71. -/

theorem BSD_ap_p79 : a_p 79 = (8 : ℤ) := by
  have h := BSD_E143_card_p79; unfold a_p; omega

/-! ## §3. Degree non-negativity — BSD_FrobeniusDegreeNonneg_OPEN p

For each prime, `BSD_FrobeniusDegreeNonneg_OPEN p = ∀ r:ℝ, r²−(a_p p:ℝ)·r+(p:ℝ) ≥ 0`.
The `key` lemma exhibits the completed-square form; `linarith [sq_nonneg ...]` closes
the goal.  All three discriminants are strictly negative. -/

/-- **`BSD_DegreeNonneg_p71`** — `BSD_FrobeniusDegreeNonneg_OPEN 71`.
    r²+9r+71 = (r+9/2)²+203/4.  Discriminant = 81−284 = −203 < 0. -/

theorem BSD_DegreeNonneg_p71 : BSD_FrobeniusDegreeNonneg_OPEN 71 := fun r => by
  have hap : (a_p 71 : ℝ) = -9 := by exact_mod_cast BSD_ap_p71
  have key : r ^ 2 - (a_p 71 : ℝ) * r + ((71 : ℕ) : ℝ) = (r + 9 / 2) ^ 2 + 203 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9 / 2)]

/-- **`BSD_DegreeNonneg_p73`** — `BSD_FrobeniusDegreeNonneg_OPEN 73`.
    r²+16r+73 = (r+8)²+9.  Discriminant = 256−292 = −36 < 0. -/

theorem BSD_DegreeNonneg_p73 : BSD_FrobeniusDegreeNonneg_OPEN 73 := fun r => by
  have hap : (a_p 73 : ℝ) = -16 := by exact_mod_cast BSD_ap_p73
  have key : r ^ 2 - (a_p 73 : ℝ) * r + ((73 : ℕ) : ℝ) = (r + 8) ^ 2 + 9 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 8)]

/-- **`BSD_DegreeNonneg_p79`** — `BSD_FrobeniusDegreeNonneg_OPEN 79`.
    r²−8r+79 = (r−4)²+63.  Discriminant = 64−316 = −252 < 0. -/

theorem BSD_DegreeNonneg_p79 : BSD_FrobeniusDegreeNonneg_OPEN 79 := fun r => by
  have hap : (a_p 79 : ℝ) = 8 := by exact_mod_cast BSD_ap_p79
  have key : r ^ 2 - (a_p 79 : ℝ) * r + ((79 : ℕ) : ℝ) = (r - 4) ^ 2 + 63 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 4)]

/-! ## §4. BSD_Hasse_OPEN — unconditional, via §V.5 bridge

Each theorem is proved by applying `BSD_hasse_of_degree_nonneg` (genesis-733, §V.5)
to the degree non-negativity from §3. -/

/-- **`BSD_Hasse_OPEN_p71`** — `BSD_Hasse_OPEN 71`: |a₇₁(E₁₄₃)| ≤ 2√71.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p71 : BSD_Hasse_OPEN 71 :=
  BSD_hasse_of_degree_nonneg 71 BSD_DegreeNonneg_p71

/-- **`BSD_Hasse_OPEN_p73`** — `BSD_Hasse_OPEN 73`: |a₇₃(E₁₄₃)| ≤ 2√73.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p73 : BSD_Hasse_OPEN 73 :=
  BSD_hasse_of_degree_nonneg 73 BSD_DegreeNonneg_p73

/-- **`BSD_Hasse_OPEN_p79`** — `BSD_Hasse_OPEN 79`: |a₇₉(E₁₄₃)| ≤ 2√79.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p79 : BSD_Hasse_OPEN 79 :=
  BSD_hasse_of_degree_nonneg 79 BSD_DegreeNonneg_p79

end Towers.BSD

