/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis740_CLOSED.lean — extracted 12 closed declarations. -/

import Towers.BSD.BSD_LFunction

private instance instFactPrime83 : Fact (83 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime89 : Fact (89 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime97 : Fact (97 : ℕ).Prime := ⟨by norm_num⟩

theorem BSD_E143_card_p83 : (E143_Finset 83).card = 83 := by decide

/-- **`BSD_E143_card_p89`** — 143a1 has exactly **96 affine 𝔽₈₉-points**.
    a₈₉ = 89−96 = −7.  Computed by `decide` over ZMod 89 × ZMod 89 (7921 pairs). -/

theorem BSD_E143_card_p89 : (E143_Finset 89).card = 96 := by decide

/-- **`BSD_E143_card_p97`** — 143a1 has exactly **110 affine 𝔽₉₇-points**.
    a₉₇ = 97−110 = −13.  Computed by `decide` over ZMod 97 × ZMod 97 (9409 pairs). -/

theorem BSD_E143_card_p97 : (E143_Finset 97).card = 110 := by decide

/-! ## §2. Exact a_p values -/

/-- **`BSD_ap_p83`** — `a_p 83 = 0`.  From a_p 83 = 83 − 83. -/

theorem BSD_ap_p83 : a_p 83 = (0 : ℤ) := by
  have h := BSD_E143_card_p83; unfold a_p; omega

/-- **`BSD_ap_p89`** — `a_p 89 = −7`.  From a_p 89 = 89 − 96. -/

theorem BSD_ap_p89 : a_p 89 = (-7 : ℤ) := by
  have h := BSD_E143_card_p89; unfold a_p; omega

/-- **`BSD_ap_p97`** — `a_p 97 = −13`.  From a_p 97 = 97 − 110. -/

theorem BSD_ap_p97 : a_p 97 = (-13 : ℤ) := by
  have h := BSD_E143_card_p97; unfold a_p; omega

/-! ## §3. Degree non-negativity — BSD_FrobeniusDegreeNonneg_OPEN p

For each prime, `BSD_FrobeniusDegreeNonneg_OPEN p = ∀ r:ℝ, r²−(a_p p:ℝ)·r+(p:ℝ) ≥ 0`.
The `key` lemma exhibits the completed-square form; `linarith [sq_nonneg ...]` closes
the goal.  All three discriminants are strictly negative. -/

/-- **`BSD_DegreeNonneg_p83`** — `BSD_FrobeniusDegreeNonneg_OPEN 83`.
    r²+0r+83 = r²+83.  Discriminant = 0−332 = −332 < 0. -/

theorem BSD_DegreeNonneg_p83 : BSD_FrobeniusDegreeNonneg_OPEN 83 := fun r => by
  have hap : (a_p 83 : ℝ) = 0 := by exact_mod_cast BSD_ap_p83
  have key : r ^ 2 - (a_p 83 : ℝ) * r + ((83 : ℕ) : ℝ) = r ^ 2 + 83 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg r]

/-- **`BSD_DegreeNonneg_p89`** — `BSD_FrobeniusDegreeNonneg_OPEN 89`.
    r²+7r+89 = (r+7/2)²+307/4.  Discriminant = 49−356 = −307 < 0. -/

theorem BSD_DegreeNonneg_p89 : BSD_FrobeniusDegreeNonneg_OPEN 89 := fun r => by
  have hap : (a_p 89 : ℝ) = -7 := by exact_mod_cast BSD_ap_p89
  have key : r ^ 2 - (a_p 89 : ℝ) * r + ((89 : ℕ) : ℝ) = (r + 7 / 2) ^ 2 + 307 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 7 / 2)]

/-- **`BSD_DegreeNonneg_p97`** — `BSD_FrobeniusDegreeNonneg_OPEN 97`.
    r²+13r+97 = (r+13/2)²+219/4.  Discriminant = 169−388 = −219 < 0. -/

theorem BSD_DegreeNonneg_p97 : BSD_FrobeniusDegreeNonneg_OPEN 97 := fun r => by
  have hap : (a_p 97 : ℝ) = -13 := by exact_mod_cast BSD_ap_p97
  have key : r ^ 2 - (a_p 97 : ℝ) * r + ((97 : ℕ) : ℝ) = (r + 13 / 2) ^ 2 + 219 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 13 / 2)]

/-! ## §4. BSD_Hasse_OPEN — unconditional, via §V.5 bridge

Each theorem is proved by applying `BSD_hasse_of_degree_nonneg` (genesis-733, §V.5)
to the degree non-negativity from §3. -/

/-- **`BSD_Hasse_OPEN_p83`** — `BSD_Hasse_OPEN 83`: |a₈₃(E₁₄₃)| ≤ 2√83.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p83 : BSD_Hasse_OPEN 83 :=
  BSD_hasse_of_degree_nonneg 83 BSD_DegreeNonneg_p83

/-- **`BSD_Hasse_OPEN_p89`** — `BSD_Hasse_OPEN 89`: |a₈₉(E₁₄₃)| ≤ 2√89.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p89 : BSD_Hasse_OPEN 89 :=
  BSD_hasse_of_degree_nonneg 89 BSD_DegreeNonneg_p89

/-- **`BSD_Hasse_OPEN_p97`** — `BSD_Hasse_OPEN 97`: |a₉₇(E₁₄₃)| ≤ 2√97.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p97 : BSD_Hasse_OPEN 97 :=
  BSD_hasse_of_degree_nonneg 97 BSD_DegreeNonneg_p97

end Towers.BSD

