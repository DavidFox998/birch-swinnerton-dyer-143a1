/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis738_CLOSED.lean — extracted 36 closed declarations. -/

import Towers.BSD.BSD_LFunction
import Towers.BSD.BSD_Frobenius_Certificate_Clean
import Mathlib.Tactic
import Towers.BSD.BSD_Targeted_Placeholders

set_option maxRecDepth 100000

private instance instFactPrime31 : Fact (31 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime37 : Fact (37 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime41 : Fact (41 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime43 : Fact (43 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime47 : Fact (47 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime53 : Fact (53 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime59 : Fact (59 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime61 : Fact (61 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime67 : Fact (67 : ℕ).Prime := ⟨by norm_num⟩


namespace Towers.BSD
theorem BSD_E143_card_p31 : (E143_Finset 31).card = 34 := by decide

/-- **`BSD_E143_card_p37`** — 143a1 has exactly **48 affine 𝔽₃₇-points**.
    a₃₇ = 37−48 = −11.  Computed by `decide` over ZMod 37 × ZMod 37 (1369 pairs). -/

theorem BSD_E143_card_p37 : (E143_Finset 37).card = 48 := by decide

/-- **`BSD_E143_card_p41`** — 143a1 has exactly **31 affine 𝔽₄₁-points**.
    a₄₁ = 41−31 = +10.  Computed by `decide` over ZMod 41 × ZMod 41 (1681 pairs). -/

theorem BSD_E143_card_p41 : (E143_Finset 41).card = 31 := by decide

/-- **`BSD_E143_card_p43`** — 143a1 has exactly **47 affine 𝔽₄₃-points**.
    a₄₃ = 43−47 = −4.  Computed by `decide` over ZMod 43 × ZMod 43 (1849 pairs). -/

theorem BSD_E143_card_p43 : (E143_Finset 43).card = 47 := by decide

/-- **`BSD_E143_card_p47`** — 143a1 has exactly **51 affine 𝔽₄₇-points**.
    a₄₇ = 47−51 = −4.  Computed by `decide` over ZMod 47 × ZMod 47 (2209 pairs). -/

theorem BSD_E143_card_p47 : (E143_Finset 47).card = 51 := by decide

/-- **`BSD_E143_card_p53`** — 143a1 has exactly **51 affine 𝔽₅₃-points**.
    a₅₃ = 53−51 = +2.  Computed by `decide` over ZMod 53 × ZMod 53 (2809 pairs). -/

theorem BSD_E143_card_p53 : (E143_Finset 53).card = 51 := by decide

/-- **`BSD_E143_card_p59`** — 143a1 has exactly **60 affine 𝔽₅₉-points**.
    a₅₉ = 59−60 = −1.  Computed by `decide` over ZMod 59 × ZMod 59 (3481 pairs). -/

theorem BSD_E143_card_p59 : (E143_Finset 59).card = 60 := by decide

/-- **`BSD_E143_card_p61`** — 143a1 has exactly **63 affine 𝔽₆₁-points**.
    a₆₁ = 61−63 = −2.  Computed by `decide` over ZMod 61 × ZMod 61 (3721 pairs). -/

theorem BSD_E143_card_p61 : (E143_Finset 61).card = 63 := by decide

/-- **`BSD_E143_card_p67`** — 143a1 has exactly **68 affine 𝔽₆₇-points**.
    a₆₇ = 67−68 = −1.  Computed by `decide` over ZMod 67 × ZMod 67 (4489 pairs). -/

theorem BSD_E143_card_p67 : (E143_Finset 67).card = 68 := by decide

/-! ## §2. Exact a_p values -/

/-- **`BSD_ap_p31`** — `a_p 31 = −3`.  From a_p 31 = 31 − 34. -/

theorem BSD_ap_p31 : a_p 31 = (-3 : ℤ) := by
  have h := BSD_E143_card_p31; unfold a_p; omega

/-- **`BSD_ap_p37`** — `a_p 37 = −11`.  From a_p 37 = 37 − 48. -/

theorem BSD_ap_p37 : a_p 37 = (-11 : ℤ) := by
  have h := BSD_E143_card_p37; unfold a_p; omega

/-- **`BSD_ap_p41`** — `a_p 41 = +10`.  From a_p 41 = 41 − 31. -/

theorem BSD_ap_p41 : a_p 41 = (10 : ℤ) := by
  have h := BSD_E143_card_p41; unfold a_p; omega

/-- **`BSD_ap_p43`** — `a_p 43 = −4`.  From a_p 43 = 43 − 47. -/

theorem BSD_ap_p43 : a_p 43 = (-4 : ℤ) := by
  have h := BSD_E143_card_p43; unfold a_p; omega

/-- **`BSD_ap_p47`** — `a_p 47 = −4`.  From a_p 47 = 47 − 51. -/

theorem BSD_ap_p47 : a_p 47 = (-4 : ℤ) := by
  have h := BSD_E143_card_p47; unfold a_p; omega

/-- **`BSD_ap_p53`** — `a_p 53 = +2`.  From a_p 53 = 53 − 51. -/

theorem BSD_ap_p53 : a_p 53 = (2 : ℤ) := by
  have h := BSD_E143_card_p53; unfold a_p; omega

/-- **`BSD_ap_p59`** — `a_p 59 = −1`.  From a_p 59 = 59 − 60. -/

theorem BSD_ap_p59 : a_p 59 = (-1 : ℤ) := by
  have h := BSD_E143_card_p59; unfold a_p; omega

/-- **`BSD_ap_p61`** — `a_p 61 = −2`.  From a_p 61 = 61 − 63. -/

theorem BSD_ap_p61 : a_p 61 = (-2 : ℤ) := by
  have h := BSD_E143_card_p61; unfold a_p; omega

/-- **`BSD_ap_p67`** — `a_p 67 = −1`.  From a_p 67 = 67 − 68. -/

theorem BSD_ap_p67 : a_p 67 = (-1 : ℤ) := by
  have h := BSD_E143_card_p67; unfold a_p; omega

/-! ## §3. Degree non-negativity — BSD_FrobeniusDegreeNonneg_OPEN p

For each prime, `BSD_FrobeniusDegreeNonneg_OPEN p = ∀ r:ℝ, r²−(a_p p:ℝ)·r+(p:ℝ) ≥ 0`.
The `key` lemma exhibits the completed-square form; `linarith [sq_nonneg ...]` closes
the goal.  All nine discriminants are strictly negative. -/

/-- **`BSD_DegreeNonneg_p31`** — `BSD_FrobeniusDegreeNonneg_OPEN 31`.
    r²+3r+31 = (r+3/2)²+115/4.  Discriminant = 9−124 = −115 < 0. -/

theorem BSD_DegreeNonneg_p31 : BSD_FrobeniusDegreeNonneg_OPEN 31 := fun r => by
  have hap : (a_p 31 : ℝ) = -3 := by exact_mod_cast BSD_ap_p31
  have key : r ^ 2 - (a_p 31 : ℝ) * r + ((31 : ℕ) : ℝ) = (r + 3 / 2) ^ 2 + 115 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 3 / 2)]

/-- **`BSD_DegreeNonneg_p37`** — `BSD_FrobeniusDegreeNonneg_OPEN 37`.
    r²+11r+37 = (r+11/2)²+27/4.  Discriminant = 121−148 = −27 < 0. -/

theorem BSD_DegreeNonneg_p37 : BSD_FrobeniusDegreeNonneg_OPEN 37 := fun r => by
  have hap : (a_p 37 : ℝ) = -11 := by exact_mod_cast BSD_ap_p37
  have key : r ^ 2 - (a_p 37 : ℝ) * r + ((37 : ℕ) : ℝ) = (r + 11 / 2) ^ 2 + 27 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11 / 2)]

/-- **`BSD_DegreeNonneg_p41`** — `BSD_FrobeniusDegreeNonneg_OPEN 41`.
    r²−10r+41 = (r−5)²+16.  Discriminant = 100−164 = −64 < 0. -/

theorem BSD_DegreeNonneg_p41 : BSD_FrobeniusDegreeNonneg_OPEN 41 := fun r => by
  have hap : (a_p 41 : ℝ) = 10 := by exact_mod_cast BSD_ap_p41
  have key : r ^ 2 - (a_p 41 : ℝ) * r + ((41 : ℕ) : ℝ) = (r - 5) ^ 2 + 16 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 5)]

/-- **`BSD_DegreeNonneg_p43`** — `BSD_FrobeniusDegreeNonneg_OPEN 43`.
    r²+4r+43 = (r+2)²+39.  Discriminant = 16−172 = −156 < 0. -/

theorem BSD_DegreeNonneg_p43 : BSD_FrobeniusDegreeNonneg_OPEN 43 := fun r => by
  have hap : (a_p 43 : ℝ) = -4 := by exact_mod_cast BSD_ap_p43
  have key : r ^ 2 - (a_p 43 : ℝ) * r + ((43 : ℕ) : ℝ) = (r + 2) ^ 2 + 39 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 2)]

/-- **`BSD_DegreeNonneg_p47`** — `BSD_FrobeniusDegreeNonneg_OPEN 47`.
    r²+4r+47 = (r+2)²+43.  Discriminant = 16−188 = −172 < 0. -/

theorem BSD_DegreeNonneg_p47 : BSD_FrobeniusDegreeNonneg_OPEN 47 := fun r => by
  have hap : (a_p 47 : ℝ) = -4 := by exact_mod_cast BSD_ap_p47
  have key : r ^ 2 - (a_p 47 : ℝ) * r + ((47 : ℕ) : ℝ) = (r + 2) ^ 2 + 43 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 2)]

/-- **`BSD_DegreeNonneg_p53`** — `BSD_FrobeniusDegreeNonneg_OPEN 53`.
    r²−2r+53 = (r−1)²+52.  Discriminant = 4−212 = −208 < 0. -/

theorem BSD_DegreeNonneg_p53 : BSD_FrobeniusDegreeNonneg_OPEN 53 := fun r => by
  have hap : (a_p 53 : ℝ) = 2 := by exact_mod_cast BSD_ap_p53
  have key : r ^ 2 - (a_p 53 : ℝ) * r + ((53 : ℕ) : ℝ) = (r - 1) ^ 2 + 52 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 1)]

/-- **`BSD_DegreeNonneg_p59`** — `BSD_FrobeniusDegreeNonneg_OPEN 59`.
    r²+r+59 = (r+1/2)²+235/4.  Discriminant = 1−236 = −235 < 0. -/

theorem BSD_DegreeNonneg_p59 : BSD_FrobeniusDegreeNonneg_OPEN 59 := fun r => by
  have hap : (a_p 59 : ℝ) = -1 := by exact_mod_cast BSD_ap_p59
  have key : r ^ 2 - (a_p 59 : ℝ) * r + ((59 : ℕ) : ℝ) = (r + 1 / 2) ^ 2 + 235 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1 / 2)]

/-- **`BSD_DegreeNonneg_p61`** — `BSD_FrobeniusDegreeNonneg_OPEN 61`.
    r²+2r+61 = (r+1)²+60.  Discriminant = 4−244 = −240 < 0. -/

theorem BSD_DegreeNonneg_p61 : BSD_FrobeniusDegreeNonneg_OPEN 61 := fun r => by
  have hap : (a_p 61 : ℝ) = -2 := by exact_mod_cast BSD_ap_p61
  have key : r ^ 2 - (a_p 61 : ℝ) * r + ((61 : ℕ) : ℝ) = (r + 1) ^ 2 + 60 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1)]

/-- **`BSD_DegreeNonneg_p67`** — `BSD_FrobeniusDegreeNonneg_OPEN 67`.
    r²+r+67 = (r+1/2)²+267/4.  Discriminant = 1−268 = −267 < 0. -/

theorem BSD_DegreeNonneg_p67 : BSD_FrobeniusDegreeNonneg_OPEN 67 := fun r => by
  have hap : (a_p 67 : ℝ) = -1 := by exact_mod_cast BSD_ap_p67
  have key : r ^ 2 - (a_p 67 : ℝ) * r + ((67 : ℕ) : ℝ) = (r + 1 / 2) ^ 2 + 267 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1 / 2)]

/-! ## §4. BSD_Hasse_OPEN — unconditional, via §V.5 bridge

Each theorem is proved by applying `BSD_hasse_of_degree_nonneg` (genesis-733, §V.5)
to the degree non-negativity from §3. -/

/-- **`BSD_Hasse_OPEN_p31`** — `BSD_Hasse_OPEN 31`: |a₃₁(E₁₄₃)| ≤ 2√31.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p31 : BSD_Hasse_OPEN 31 :=
  BSD_hasse_of_degree_nonneg 31 BSD_DegreeNonneg_p31

/-- **`BSD_Hasse_OPEN_p37`** — `BSD_Hasse_OPEN 37`: |a₃₇(E₁₄₃)| ≤ 2√37.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p37 : BSD_Hasse_OPEN 37 :=
  BSD_hasse_of_degree_nonneg 37 BSD_DegreeNonneg_p37

/-- **`BSD_Hasse_OPEN_p41`** — `BSD_Hasse_OPEN 41`: |a₄₁(E₁₄₃)| ≤ 2√41.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p41 : BSD_Hasse_OPEN 41 :=
  BSD_hasse_of_degree_nonneg 41 BSD_DegreeNonneg_p41

/-- **`BSD_Hasse_OPEN_p43`** — `BSD_Hasse_OPEN 43`: |a₄₃(E₁₄₃)| ≤ 2√43.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p43 : BSD_Hasse_OPEN 43 :=
  BSD_hasse_of_degree_nonneg 43 BSD_DegreeNonneg_p43

/-- **`BSD_Hasse_OPEN_p47`** — `BSD_Hasse_OPEN 47`: |a₄₇(E₁₄₃)| ≤ 2√47.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p47 : BSD_Hasse_OPEN 47 :=
  BSD_hasse_of_degree_nonneg 47 BSD_DegreeNonneg_p47

/-- **`BSD_Hasse_OPEN_p53`** — `BSD_Hasse_OPEN 53`: |a₅₃(E₁₄₃)| ≤ 2√53.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p53 : BSD_Hasse_OPEN 53 :=
  BSD_hasse_of_degree_nonneg 53 BSD_DegreeNonneg_p53

/-- **`BSD_Hasse_OPEN_p59`** — `BSD_Hasse_OPEN 59`: |a₅₉(E₁₄₃)| ≤ 2√59.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p59 : BSD_Hasse_OPEN 59 :=
  BSD_hasse_of_degree_nonneg 59 BSD_DegreeNonneg_p59

/-- **`BSD_Hasse_OPEN_p61`** — `BSD_Hasse_OPEN 61`: |a₆₁(E₁₄₃)| ≤ 2√61.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p61 : BSD_Hasse_OPEN 61 :=
  BSD_hasse_of_degree_nonneg 61 BSD_DegreeNonneg_p61

/-- **`BSD_Hasse_OPEN_p67`** — `BSD_Hasse_OPEN 67`: |a₆₇(E₁₄₃)| ≤ 2√67.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p67 : BSD_Hasse_OPEN 67 :=
  BSD_hasse_of_degree_nonneg 67 BSD_DegreeNonneg_p67

end Towers.BSD

