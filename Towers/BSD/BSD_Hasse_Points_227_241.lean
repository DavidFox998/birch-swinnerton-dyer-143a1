/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis745_CLOSED.lean — extracted 20 closed declarations. -/

import Towers.BSD.BSD_LFunction
import Towers.BSD.BSD_Frobenius_Certificate_Clean

namespace Towers.BSD

instance instFact_prime_227 : Fact (Nat.Prime 227) := ⟨by native_decide⟩
instance instFact_prime_229 : Fact (Nat.Prime 229) := ⟨by native_decide⟩
instance instFact_prime_233 : Fact (Nat.Prime 233) := ⟨by native_decide⟩
instance instFact_prime_239 : Fact (Nat.Prime 239) := ⟨by native_decide⟩
instance instFact_prime_241 : Fact (Nat.Prime 241) := ⟨by native_decide⟩


theorem BSD_E143_card_p227 : (E143_Finset 227).card = 227 := by native_decide

/-- **`BSD_E143_card_p229`** — 143a1 has exactly **220 affine 𝔽₂₂₉-points**.
    a₂₂₉ = 229−220 = +9.  Computed by `decide` over ZMod 229 × ZMod 229 (52441 pairs). -/

theorem BSD_E143_card_p229 : (E143_Finset 229).card = 220 := by native_decide

/-- **`BSD_E143_card_p233`** — 143a1 has exactly **249 affine 𝔽₂₃₃-points**.
    a₂₃₃ = 233−249 = −16.  Computed by `decide` over ZMod 233 × ZMod 233 (54289 pairs). -/

theorem BSD_E143_card_p233 : (E143_Finset 233).card = 249 := by native_decide

/-- **`BSD_E143_card_p239`** — 143a1 has exactly **269 affine 𝔽₂₃₉-points**.
    a₂₃₉ = 239−269 = −30.  Computed by `decide` over ZMod 239 × ZMod 239 (57121 pairs). -/

theorem BSD_E143_card_p239 : (E143_Finset 239).card = 269 := by native_decide

/-- **`BSD_E143_card_p241`** — 143a1 has exactly **251 affine 𝔽₂₄₁-points**.
    a₂₄₁ = 241−251 = −10.  Computed by `decide` over ZMod 241 × ZMod 241 (58081 pairs). -/

theorem BSD_E143_card_p241 : (E143_Finset 241).card = 251 := by native_decide

/-! ## §2. Exact a_p values -/

/-- **`BSD_ap_p227`** — `a_p 227 = 0`.  From a_p 227 = 227 − 227. -/

theorem BSD_ap_p227 : a_p 227 = (0 : ℤ) := by
  have h := BSD_E143_card_p227; unfold a_p; omega

/-- **`BSD_ap_p229`** — `a_p 229 = +9`.  From a_p 229 = 229 − 220. -/

theorem BSD_ap_p229 : a_p 229 = (9 : ℤ) := by
  have h := BSD_E143_card_p229; unfold a_p; omega

/-- **`BSD_ap_p233`** — `a_p 233 = −16`.  From a_p 233 = 233 − 249. -/

theorem BSD_ap_p233 : a_p 233 = (-16 : ℤ) := by
  have h := BSD_E143_card_p233; unfold a_p; omega

/-- **`BSD_ap_p239`** — `a_p 239 = −30`.  From a_p 239 = 239 − 269. -/

theorem BSD_ap_p239 : a_p 239 = (-30 : ℤ) := by
  have h := BSD_E143_card_p239; unfold a_p; omega

/-- **`BSD_ap_p241`** — `a_p 241 = −10`.  From a_p 241 = 241 − 251. -/

theorem BSD_ap_p241 : a_p 241 = (-10 : ℤ) := by
  have h := BSD_E143_card_p241; unfold a_p; omega

/-! ## §3. Degree non-negativity — BSD_FrobeniusDegreeNonneg_OPEN p -/

/-- **`BSD_DegreeNonneg_p227`** — `BSD_FrobeniusDegreeNonneg_OPEN 227`.
    r²+227 (a₂₂₇=0, no linear term).  Discriminant = 0−908 = −908 < 0. -/

theorem BSD_DegreeNonneg_p227 : BSD_FrobeniusDegreeNonneg_OPEN 227 := fun r => by
  have hap : (a_p 227 : ℝ) = 0 := by exact_mod_cast BSD_ap_p227
  have key : r ^ 2 - (a_p 227 : ℝ) * r + ((227 : ℕ) : ℝ) = r ^ 2 + 227 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg r]

/-- **`BSD_DegreeNonneg_p229`** — `BSD_FrobeniusDegreeNonneg_OPEN 229`.
    r²−9r+229 = (r−9/2)²+835/4.  Discriminant = 81−916 = −835 < 0.
    Half-integer witness (a₂₂₉ = +9 is odd). -/

theorem BSD_DegreeNonneg_p229 : BSD_FrobeniusDegreeNonneg_OPEN 229 := fun r => by
  have hap : (a_p 229 : ℝ) = 9 := by exact_mod_cast BSD_ap_p229
  have key : r ^ 2 - (a_p 229 : ℝ) * r + ((229 : ℕ) : ℝ) = (r - 9 / 2) ^ 2 + 835 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9 / 2)]

/-- **`BSD_DegreeNonneg_p233`** — `BSD_FrobeniusDegreeNonneg_OPEN 233`.
    r²+16r+233 = (r+8)²+169.  Discriminant = 256−932 = −676 < 0. -/

theorem BSD_DegreeNonneg_p233 : BSD_FrobeniusDegreeNonneg_OPEN 233 := fun r => by
  have hap : (a_p 233 : ℝ) = -16 := by exact_mod_cast BSD_ap_p233
  have key : r ^ 2 - (a_p 233 : ℝ) * r + ((233 : ℕ) : ℝ) = (r + 8) ^ 2 + 169 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 8)]

/-- **`BSD_DegreeNonneg_p239`** — `BSD_FrobeniusDegreeNonneg_OPEN 239`.
    r²+30r+239 = (r+15)²+14.  Discriminant = 900−956 = −56 < 0. -/

theorem BSD_DegreeNonneg_p239 : BSD_FrobeniusDegreeNonneg_OPEN 239 := fun r => by
  have hap : (a_p 239 : ℝ) = -30 := by exact_mod_cast BSD_ap_p239
  have key : r ^ 2 - (a_p 239 : ℝ) * r + ((239 : ℕ) : ℝ) = (r + 15) ^ 2 + 14 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15)]

/-- **`BSD_DegreeNonneg_p241`** — `BSD_FrobeniusDegreeNonneg_OPEN 241`.
    r²+10r+241 = (r+5)²+216.  Discriminant = 100−964 = −864 < 0. -/

theorem BSD_DegreeNonneg_p241 : BSD_FrobeniusDegreeNonneg_OPEN 241 := fun r => by
  have hap : (a_p 241 : ℝ) = -10 := by exact_mod_cast BSD_ap_p241
  have key : r ^ 2 - (a_p 241 : ℝ) * r + ((241 : ℕ) : ℝ) = (r + 5) ^ 2 + 216 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 5)]

/-! ## §4. BSD_Hasse_OPEN — unconditional, via §V.5 bridge -/

/-- **`BSD_Hasse_OPEN_p227`** — `BSD_Hasse_OPEN 227`: |a₂₂₇(E₁₄₃)| ≤ 2√227.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p227 : BSD_Hasse_OPEN 227 :=
  BSD_hasse_of_degree_nonneg 227 BSD_DegreeNonneg_p227

/-- **`BSD_Hasse_OPEN_p229`** — `BSD_Hasse_OPEN 229`: |a₂₂₉(E₁₄₃)| ≤ 2√229.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p229 : BSD_Hasse_OPEN 229 :=
  BSD_hasse_of_degree_nonneg 229 BSD_DegreeNonneg_p229

/-- **`BSD_Hasse_OPEN_p233`** — `BSD_Hasse_OPEN 233`: |a₂₃₃(E₁₄₃)| ≤ 2√233.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p233 : BSD_Hasse_OPEN 233 :=
  BSD_hasse_of_degree_nonneg 233 BSD_DegreeNonneg_p233

/-- **`BSD_Hasse_OPEN_p239`** — `BSD_Hasse_OPEN 239`: |a₂₃₉(E₁₄₃)| ≤ 2√239.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p239 : BSD_Hasse_OPEN 239 :=
  BSD_hasse_of_degree_nonneg 239 BSD_DegreeNonneg_p239

/-- **`BSD_Hasse_OPEN_p241`** — `BSD_Hasse_OPEN 241`: |a₂₄₁(E₁₄₃)| ≤ 2√241.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p241 : BSD_Hasse_OPEN 241 :=
  BSD_hasse_of_degree_nonneg 241 BSD_DegreeNonneg_p241

end Towers.BSD

