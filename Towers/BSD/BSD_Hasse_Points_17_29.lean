/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis736_CLOSED.lean — extracted 16 closed declarations. -/

import Towers.BSD.BSD_LFunction
import Towers.BSD.BSD_Frobenius_Certificate_Clean

namespace Towers.BSD

instance instFact_prime_17 : Fact (Nat.Prime 17) := ⟨by decide⟩
instance instFact_prime_19 : Fact (Nat.Prime 19) := ⟨by decide⟩
instance instFact_prime_23 : Fact (Nat.Prime 23) := ⟨by decide⟩
instance instFact_prime_29 : Fact (Nat.Prime 29) := ⟨by decide⟩


theorem BSD_E143_card_p17 : (E143_Finset 17).card = 21 := by decide

/-- **`BSD_E143_card_p19`** — 143a1 has exactly **17 affine 𝔽₁₉-points**.
    a₁₉ = 19−17 = +2.  Computed by `decide` over ZMod 19 × ZMod 19 (361 pairs). -/

theorem BSD_E143_card_p19 : (E143_Finset 19).card = 17 := by decide

/-- **`BSD_E143_card_p23`** — 143a1 has exactly **16 affine 𝔽₂₃-points**.
    a₂₃ = 23−16 = +7.  Computed by `decide` over ZMod 23 × ZMod 23 (529 pairs). -/

theorem BSD_E143_card_p23 : (E143_Finset 23).card = 16 := by decide

/-- **`BSD_E143_card_p29`** — 143a1 has exactly **31 affine 𝔽₂₉-points**.
    a₂₉ = 29−31 = −2.  Computed by `decide` over ZMod 29 × ZMod 29 (841 pairs). -/

theorem BSD_E143_card_p29 : (E143_Finset 29).card = 31 := by decide

/-! ## §2. Exact a_p values -/

/-- **`BSD_ap_p17`** — `a_p 17 = −4`.  From a_p 17 = 17 − 21. -/

theorem BSD_ap_p17 : a_p 17 = (-4 : ℤ) := by
  have h := BSD_E143_card_p17; unfold a_p; omega

/-- **`BSD_ap_p19`** — `a_p 19 = +2`.  From a_p 19 = 19 − 17. -/

theorem BSD_ap_p19 : a_p 19 = (2 : ℤ) := by
  have h := BSD_E143_card_p19; unfold a_p; omega

/-- **`BSD_ap_p23`** — `a_p 23 = +7`.  From a_p 23 = 23 − 16. -/

theorem BSD_ap_p23 : a_p 23 = (7 : ℤ) := by
  have h := BSD_E143_card_p23; unfold a_p; omega

/-- **`BSD_ap_p29`** — `a_p 29 = −2`.  From a_p 29 = 29 − 31. -/

theorem BSD_ap_p29 : a_p 29 = (-2 : ℤ) := by
  have h := BSD_E143_card_p29; unfold a_p; omega

/-! ## §3. Degree non-negativity — BSD_FrobeniusDegreeNonneg_OPEN p

For each prime, `BSD_FrobeniusDegreeNonneg_OPEN p = ∀ r:ℝ, r²−(a_p p:ℝ)·r+(p:ℝ) ≥ 0`.
The `key` lemma exhibits the completed-square form; `linarith [sq_nonneg ...]` closes
the goal.  All four discriminants are strictly negative (Hasse bound verified). -/

/-- **`BSD_DegreeNonneg_p17`** — `BSD_FrobeniusDegreeNonneg_OPEN 17`.
    r²+4r+17 = (r+2)²+13.  Discriminant = 16−68 = −52 < 0.  Witness: sq_nonneg (r+2). -/

theorem BSD_DegreeNonneg_p17 : BSD_FrobeniusDegreeNonneg_OPEN 17 := fun r => by
  have hap : (a_p 17 : ℝ) = -4 := by exact_mod_cast BSD_ap_p17
  have key : r ^ 2 - (a_p 17 : ℝ) * r + ((17 : ℕ) : ℝ) = (r + 2) ^ 2 + 13 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 2)]

/-- **`BSD_DegreeNonneg_p19`** — `BSD_FrobeniusDegreeNonneg_OPEN 19`.
    r²−2r+19 = (r−1)²+18.  Discriminant = 4−76 = −72 < 0.  Witness: sq_nonneg (r−1). -/

theorem BSD_DegreeNonneg_p19 : BSD_FrobeniusDegreeNonneg_OPEN 19 := fun r => by
  have hap : (a_p 19 : ℝ) = 2 := by exact_mod_cast BSD_ap_p19
  have key : r ^ 2 - (a_p 19 : ℝ) * r + ((19 : ℕ) : ℝ) = (r - 1) ^ 2 + 18 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 1)]

/-- **`BSD_DegreeNonneg_p23`** — `BSD_FrobeniusDegreeNonneg_OPEN 23`.
    r²−7r+23 = (r−7/2)²+43/4.  Discriminant = 49−92 = −43 < 0.  Witness: sq_nonneg (r−7/2). -/

theorem BSD_DegreeNonneg_p23 : BSD_FrobeniusDegreeNonneg_OPEN 23 := fun r => by
  have hap : (a_p 23 : ℝ) = 7 := by exact_mod_cast BSD_ap_p23
  have key : r ^ 2 - (a_p 23 : ℝ) * r + ((23 : ℕ) : ℝ) = (r - 7 / 2) ^ 2 + 43 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 7 / 2)]

/-- **`BSD_DegreeNonneg_p29`** — `BSD_FrobeniusDegreeNonneg_OPEN 29`.
    r²+2r+29 = (r+1)²+28.  Discriminant = 4−116 = −112 < 0.  Witness: sq_nonneg (r+1). -/

theorem BSD_DegreeNonneg_p29 : BSD_FrobeniusDegreeNonneg_OPEN 29 := fun r => by
  have hap : (a_p 29 : ℝ) = -2 := by exact_mod_cast BSD_ap_p29
  have key : r ^ 2 - (a_p 29 : ℝ) * r + ((29 : ℕ) : ℝ) = (r + 1) ^ 2 + 28 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1)]

/-! ## §4. BSD_Hasse_OPEN — unconditional, via §V.5 bridge

Each theorem is proved by applying `BSD_hasse_of_degree_nonneg` (genesis-733, §V.5)
to the degree non-negativity from §3.  First concrete use of the §V.5 bridge
for the range p ∈ {17,19,23,29}. -/

/-- **`BSD_Hasse_OPEN_p17`** — `BSD_Hasse_OPEN 17`: |a₁₇(E₁₄₃)| ≤ 2√17.
    UNCONDITIONAL, 0 sorry, classical trio.  Route: decide → omega → linarith/sq →
    BSD_hasse_of_degree_nonneg. -/

theorem BSD_Hasse_OPEN_p17 : BSD_Hasse_OPEN 17 :=
  BSD_hasse_of_degree_nonneg 17 BSD_DegreeNonneg_p17

/-- **`BSD_Hasse_OPEN_p19`** — `BSD_Hasse_OPEN 19`: |a₁₉(E₁₄₃)| ≤ 2√19.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p19 : BSD_Hasse_OPEN 19 :=
  BSD_hasse_of_degree_nonneg 19 BSD_DegreeNonneg_p19

/-- **`BSD_Hasse_OPEN_p23`** — `BSD_Hasse_OPEN 23`: |a₂₃(E₁₄₃)| ≤ 2√23.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p23 : BSD_Hasse_OPEN 23 :=
  BSD_hasse_of_degree_nonneg 23 BSD_DegreeNonneg_p23

/-- **`BSD_Hasse_OPEN_p29`** — `BSD_Hasse_OPEN 29`: |a₂₉(E₁₄₃)| ≤ 2√29.
    UNCONDITIONAL, 0 sorry, classical trio. -/

theorem BSD_Hasse_OPEN_p29 : BSD_Hasse_OPEN 29 :=
  BSD_hasse_of_degree_nonneg 29 BSD_DegreeNonneg_p29

end Towers.BSD

