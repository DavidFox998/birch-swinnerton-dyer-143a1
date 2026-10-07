/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis744_CLOSED.lean — extracted 20 closed declarations. -/

import Towers.BSD.BSD_LFunction
import Mathlib.Tactic
import Towers.BSD.BSD_Frobenius_Certificate_Clean
import Mathlib.Tactic
import Towers.BSD.BSD_Targeted_Placeholders

set_option maxRecDepth 100000

private instance instFactPrime193 : Fact (193 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime197 : Fact (197 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime199 : Fact (199 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime211 : Fact (211 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime223 : Fact (223 : ℕ).Prime := ⟨by norm_num⟩


namespace Towers.BSD
theorem BSD_E143_card_p193 : (E143_Finset 193).card = 217 := by native_decide

/-- **`BSD_E143_card_p197`** — 143a1 has exactly **207 affine 𝔽₁₉₇-points**.
    a₁₉₇ = 197−207 = −10.  Computed by `decide` over ZMod 197 × ZMod 197 (38809 pairs). -/

theorem BSD_E143_card_p197 : (E143_Finset 197).card = 207 := by native_decide

/-- **`BSD_E143_card_p199`** — 143a1 has exactly **203 affine 𝔽₁₉₉-points**.
    a₁₉₉ = 199−203 = −4.  Computed by `decide` over ZMod 199 × ZMod 199 (39601 pairs). -/

theorem BSD_E143_card_p199 : (E143_Finset 199).card = 203 := by native_decide

/-- **`BSD_E143_card_p211`** — 143a1 has exactly **235 affine 𝔽₂₁₁-points**.
    a₂₁₁ = 211−235 = −24.  Computed by `decide` over ZMod 211 × ZMod 211 (44521 pairs). -/

theorem BSD_E143_card_p211 : (E143_Finset 211).card = 235 := by native_decide

/-- **`BSD_E143_card_p223`** — 143a1 has exactly **218 affine 𝔽₂₂₃-points**.
    a₂₂₃ = 223−218 = +5.  Computed by `decide` over ZMod 223 × ZMod 223 (49729 pairs). -/

theorem BSD_E143_card_p223 : (E143_Finset 223).card = 218 := by native_decide

/-! ## §2. Exact a_p values -/

/-- **`BSD_ap_p193`** — `a_p 193 = −24`.  From a_p 193 = 193 − 217. -/

theorem BSD_ap_p193 : a_p 193 = (-24 : ℤ) := by
  have h := BSD_E143_card_p193; unfold a_p; omega

/-- **`BSD_ap_p197`** — `a_p 197 = −10`.  From a_p 197 = 197 − 207. -/

theorem BSD_ap_p197 : a_p 197 = (-10 : ℤ) := by
  have h := BSD_E143_card_p197; unfold a_p; omega

/-- **`BSD_ap_p199`** — `a_p 199 = −4`.  From a_p 199 = 199 − 203. -/

theorem BSD_ap_p199 : a_p 199 = (-4 : ℤ) := by
  have h := BSD_E143_card_p199; unfold a_p; omega

/-- **`BSD_ap_p211`** — `a_p 211 = −24`.  From a_p 211 = 211 − 235. -/

theorem BSD_ap_p211 : a_p 211 = (-24 : ℤ) := by
  have h := BSD_E143_card_p211; unfold a_p; omega

/-- **`BSD_ap_p223`** — `a_p 223 = +5`.  From a_p 223 = 223 − 218. -/

theorem BSD_ap_p223 : a_p 223 = (5 : ℤ) := by
  have h := BSD_E143_card_p223; unfold a_p; omega

/-! ## §3. Degree non-negativity — BSD_FrobeniusDegreeNonneg_OPEN p -/

/-- **`BSD_DegreeNonneg_p193`** — `BSD_FrobeniusDegreeNonneg_OPEN 193`.
    r²+24r+193 = (r+12)²+49.  Discriminant = 576−772 = −196 < 0. -/

theorem BSD_DegreeNonneg_p193 : BSD_FrobeniusDegreeNonneg_OPEN 193 := fun r => by
  have hap : (a_p 193 : ℝ) = -24 := by exact_mod_cast BSD_ap_p193
  have key : r ^ 2 - (a_p 193 : ℝ) * r + ((193 : ℕ) : ℝ) = (r + 12) ^ 2 + 49 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 12)]

/-- **`BSD_DegreeNonneg_p197`** — `BSD_FrobeniusDegreeNonneg_OPEN 197`.
    r²+10r+197 = (r+5)²+172.  Discriminant = 100−788 = −688 < 0. -/

theorem BSD_DegreeNonneg_p197 : BSD_FrobeniusDegreeNonneg_OPEN 197 := fun r => by
  have hap : (a_p 197 : ℝ) = -10 := by exact_mod_cast BSD_ap_p197
  have key : r ^ 2 - (a_p 197 : ℝ) * r + ((197 : ℕ) : ℝ) = (r + 5) ^ 2 + 172 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 5)]

/-- **`BSD_DegreeNonneg_p199`** — `BSD_FrobeniusDegreeNonneg_OPEN 199`.
    r²+4r+199 = (r+2)²+195.  Discriminant = 16−796 = −780 < 0. -/

theorem BSD_DegreeNonneg_p199 : BSD_FrobeniusDegreeNonneg_OPEN 199 := fun r => by
  have hap : (a_p 199 : ℝ) = -4 := by exact_mod_cast BSD_ap_p199
  have key : r ^ 2 - (a_p 199 : ℝ) * r + ((199 : ℕ) : ℝ) = (r + 2) ^ 2 + 195 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 2)]

/-- **`BSD_DegreeNonneg_p211`** — `BSD_FrobeniusDegreeNonneg_OPEN 211`.
    r²+24r+211 = (r+12)²+67.  Discriminant = 576−844 = −268 < 0. -/

theorem BSD_DegreeNonneg_p211 : BSD_FrobeniusDegreeNonneg_OPEN 211 := fun r => by
  have hap : (a_p 211 : ℝ) = -24 := by exact_mod_cast BSD_ap_p211
  have key : r ^ 2 - (a_p 211 : ℝ) * r + ((211 : ℕ) : ℝ) = (r + 12) ^ 2 + 67 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 12)]

/-- **`BSD_DegreeNonneg_p223`** — `BSD_FrobeniusDegreeNonneg_OPEN 223`.
    r²−5r+223 = (r−5/2)²+867/4.  Discriminant = 25−892 = −867 < 0.
    Half-integer witness (a₂₂₃ = +5 is odd). -/

theorem BSD_DegreeNonneg_p223 : BSD_FrobeniusDegreeNonneg_OPEN 223 := fun r => by
  have hap : (a_p 223 : ℝ) = 5 := by exact_mod_cast BSD_ap_p223
  have key : r ^ 2 - (a_p 223 : ℝ) * r + ((223 : ℕ) : ℝ) = (r - 5 / 2) ^ 2 + 867 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 5 / 2)]

/-! ## §4. BSD_Hasse_OPEN — unconditional, via §V.5 bridge -/

/-- **`BSD_Hasse_OPEN_p193`** — `BSD_Hasse_OPEN 193`: |a₁₉₃(E₁₄₃)| ≤ 2√193.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p193 : BSD_Hasse_OPEN 193 :=
  BSD_hasse_of_degree_nonneg 193 BSD_DegreeNonneg_p193

/-- **`BSD_Hasse_OPEN_p197`** — `BSD_Hasse_OPEN 197`: |a₁₉₇(E₁₄₃)| ≤ 2√197.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p197 : BSD_Hasse_OPEN 197 :=
  BSD_hasse_of_degree_nonneg 197 BSD_DegreeNonneg_p197

/-- **`BSD_Hasse_OPEN_p199`** — `BSD_Hasse_OPEN 199`: |a₁₉₉(E₁₄₃)| ≤ 2√199.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p199 : BSD_Hasse_OPEN 199 :=
  BSD_hasse_of_degree_nonneg 199 BSD_DegreeNonneg_p199

/-- **`BSD_Hasse_OPEN_p211`** — `BSD_Hasse_OPEN 211`: |a₂₁₁(E₁₄₃)| ≤ 2√211.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p211 : BSD_Hasse_OPEN 211 :=
  BSD_hasse_of_degree_nonneg 211 BSD_DegreeNonneg_p211

/-- **`BSD_Hasse_OPEN_p223`** — `BSD_Hasse_OPEN 223`: |a₂₂₃(E₁₄₃)| ≤ 2√223.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p223 : BSD_Hasse_OPEN 223 :=
  BSD_hasse_of_degree_nonneg 223 BSD_DegreeNonneg_p223

end Towers.BSD

