/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis741_CLOSED.lean — extracted 20 closed declarations. -/

import Towers.BSD.BSD_LFunction
import Towers.BSD.BSD_Frobenius_Certificate_Clean

private instance instFactPrime101 : Fact (101 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime103 : Fact (103 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime107 : Fact (107 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime109 : Fact (109 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime113 : Fact (113 : ℕ).Prime := ⟨by norm_num⟩

theorem BSD_E143_card_p101 : (E143_Finset 101).card = 83 := by decide

/-- **`BSD_E143_card_p103`** — 143a1 has exactly **95 affine 𝔽₁₀₃-points**.
    a₁₀₃ = 103−95 = +8.  Computed by `decide` over ZMod 103 × ZMod 103 (10609 pairs). -/

theorem BSD_E143_card_p103 : (E143_Finset 103).card = 95 := by decide

/-- **`BSD_E143_card_p107`** — 143a1 has exactly **99 affine 𝔽₁₀₇-points**.
    a₁₀₇ = 107−99 = +8.  Computed by `decide` over ZMod 107 × ZMod 107 (11449 pairs). -/

theorem BSD_E143_card_p107 : (E143_Finset 107).card = 99 := by decide

/-- **`BSD_E143_card_p109`** — 143a1 has exactly **105 affine 𝔽₁₀₉-points**.
    a₁₀₉ = 109−105 = +4.  Computed by `decide` over ZMod 109 × ZMod 109 (11881 pairs). -/

theorem BSD_E143_card_p109 : (E143_Finset 109).card = 105 := by decide

/-- **`BSD_E143_card_p113`** — 143a1 has exactly **112 affine 𝔽₁₁₃-points**.
    a₁₁₃ = 113−112 = +1.  Computed by `decide` over ZMod 113 × ZMod 113 (12769 pairs). -/

theorem BSD_E143_card_p113 : (E143_Finset 113).card = 112 := by decide

/-! ## §2. Exact a_p values -/

/-- **`BSD_ap_p101`** — `a_p 101 = +18`.  From a_p 101 = 101 − 83. -/

theorem BSD_ap_p101 : a_p 101 = (18 : ℤ) := by
  have h := BSD_E143_card_p101; unfold a_p; omega

/-- **`BSD_ap_p103`** — `a_p 103 = +8`.  From a_p 103 = 103 − 95. -/

theorem BSD_ap_p103 : a_p 103 = (8 : ℤ) := by
  have h := BSD_E143_card_p103; unfold a_p; omega

/-- **`BSD_ap_p107`** — `a_p 107 = +8`.  From a_p 107 = 107 − 99. -/

theorem BSD_ap_p107 : a_p 107 = (8 : ℤ) := by
  have h := BSD_E143_card_p107; unfold a_p; omega

/-- **`BSD_ap_p109`** — `a_p 109 = +4`.  From a_p 109 = 109 − 105. -/

theorem BSD_ap_p109 : a_p 109 = (4 : ℤ) := by
  have h := BSD_E143_card_p109; unfold a_p; omega

/-- **`BSD_ap_p113`** — `a_p 113 = +1`.  From a_p 113 = 113 − 112. -/

theorem BSD_ap_p113 : a_p 113 = (1 : ℤ) := by
  have h := BSD_E143_card_p113; unfold a_p; omega

/-! ## §3. Degree non-negativity — BSD_FrobeniusDegreeNonneg_OPEN p -/

/-- **`BSD_DegreeNonneg_p101`** — `BSD_FrobeniusDegreeNonneg_OPEN 101`.
    r²−18r+101 = (r−9)²+20.  Discriminant = 324−404 = −80 < 0. -/

theorem BSD_DegreeNonneg_p101 : BSD_FrobeniusDegreeNonneg_OPEN 101 := fun r => by
  have hap : (a_p 101 : ℝ) = 18 := by exact_mod_cast BSD_ap_p101
  have key : r ^ 2 - (a_p 101 : ℝ) * r + ((101 : ℕ) : ℝ) = (r - 9) ^ 2 + 20 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

/-- **`BSD_DegreeNonneg_p103`** — `BSD_FrobeniusDegreeNonneg_OPEN 103`.
    r²−8r+103 = (r−4)²+87.  Discriminant = 64−412 = −348 < 0. -/

theorem BSD_DegreeNonneg_p103 : BSD_FrobeniusDegreeNonneg_OPEN 103 := fun r => by
  have hap : (a_p 103 : ℝ) = 8 := by exact_mod_cast BSD_ap_p103
  have key : r ^ 2 - (a_p 103 : ℝ) * r + ((103 : ℕ) : ℝ) = (r - 4) ^ 2 + 87 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 4)]

/-- **`BSD_DegreeNonneg_p107`** — `BSD_FrobeniusDegreeNonneg_OPEN 107`.
    r²−8r+107 = (r−4)²+91.  Discriminant = 64−428 = −364 < 0. -/

theorem BSD_DegreeNonneg_p107 : BSD_FrobeniusDegreeNonneg_OPEN 107 := fun r => by
  have hap : (a_p 107 : ℝ) = 8 := by exact_mod_cast BSD_ap_p107
  have key : r ^ 2 - (a_p 107 : ℝ) * r + ((107 : ℕ) : ℝ) = (r - 4) ^ 2 + 91 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 4)]

/-- **`BSD_DegreeNonneg_p109`** — `BSD_FrobeniusDegreeNonneg_OPEN 109`.
    r²−4r+109 = (r−2)²+105.  Discriminant = 16−436 = −420 < 0. -/

theorem BSD_DegreeNonneg_p109 : BSD_FrobeniusDegreeNonneg_OPEN 109 := fun r => by
  have hap : (a_p 109 : ℝ) = 4 := by exact_mod_cast BSD_ap_p109
  have key : r ^ 2 - (a_p 109 : ℝ) * r + ((109 : ℕ) : ℝ) = (r - 2) ^ 2 + 105 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 2)]

/-- **`BSD_DegreeNonneg_p113`** — `BSD_FrobeniusDegreeNonneg_OPEN 113`.
    r²−r+113 = (r−1/2)²+451/4.  Discriminant = 1−452 = −451 < 0.
    Half-integer witness (a₁₁₃ = +1 is odd). -/

theorem BSD_DegreeNonneg_p113 : BSD_FrobeniusDegreeNonneg_OPEN 113 := fun r => by
  have hap : (a_p 113 : ℝ) = 1 := by exact_mod_cast BSD_ap_p113
  have key : r ^ 2 - (a_p 113 : ℝ) * r + ((113 : ℕ) : ℝ) = (r - 1 / 2) ^ 2 + 451 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 1 / 2)]

/-! ## §4. BSD_Hasse_OPEN — unconditional, via §V.5 bridge -/

/-- **`BSD_Hasse_OPEN_p101`** — `BSD_Hasse_OPEN 101`: |a₁₀₁(E₁₄₃)| ≤ 2√101.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p101 : BSD_Hasse_OPEN 101 :=
  BSD_hasse_of_degree_nonneg 101 BSD_DegreeNonneg_p101

/-- **`BSD_Hasse_OPEN_p103`** — `BSD_Hasse_OPEN 103`: |a₁₀₃(E₁₄₃)| ≤ 2√103.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p103 : BSD_Hasse_OPEN 103 :=
  BSD_hasse_of_degree_nonneg 103 BSD_DegreeNonneg_p103

/-- **`BSD_Hasse_OPEN_p107`** — `BSD_Hasse_OPEN 107`: |a₁₀₇(E₁₄₃)| ≤ 2√107.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p107 : BSD_Hasse_OPEN 107 :=
  BSD_hasse_of_degree_nonneg 107 BSD_DegreeNonneg_p107

/-- **`BSD_Hasse_OPEN_p109`** — `BSD_Hasse_OPEN 109`: |a₁₀₉(E₁₄₃)| ≤ 2√109.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p109 : BSD_Hasse_OPEN 109 :=
  BSD_hasse_of_degree_nonneg 109 BSD_DegreeNonneg_p109

/-- **`BSD_Hasse_OPEN_p113`** — `BSD_Hasse_OPEN 113`: |a₁₁₃(E₁₄₃)| ≤ 2√113.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p113 : BSD_Hasse_OPEN 113 :=
  BSD_hasse_of_degree_nonneg 113 BSD_DegreeNonneg_p113

end Towers.BSD

