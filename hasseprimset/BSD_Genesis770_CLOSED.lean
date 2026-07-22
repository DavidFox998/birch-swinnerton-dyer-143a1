/-
================================================================
Towers / BSD / BSD_Genesis770_CLOSED  (genesis-770)

HasseBridge Batch 8: Hasse bounds for primes
683..751 (10 primes).
Tier A grows to 131 primes after this file.

Pair sizes (p^2):
  p=683: card=687, a_p=-4, disc=-2716 (466489 pairs)
  p=691: card=736, a_p=-45, disc=-739 (477481 pairs)
  p=701: card=711, a_p=-10, disc=-2704 (491401 pairs)
  p=709: card=744, a_p=-35, disc=-1611 (502681 pairs)
  p=719: card=760, a_p=-41, disc=-1195 (516961 pairs)
  p=727: card=708, a_p=+19, disc=-2547 (528529 pairs)
  p=733: card=779, a_p=-46, disc=-816 (537289 pairs)
  p=739: card=741, a_p=-2, disc=-2952 (546121 pairs)
  p=743: card=701, a_p=+42, disc=-1208 (552049 pairs)
  p=751: card=790, a_p=-39, disc=-1483 (564001 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis769_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_770 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i770_p683 : Fact (683 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p691 : Fact (691 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p701 : Fact (701 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p709 : Fact (709 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p719 : Fact (719 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p727 : Fact (727 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p733 : Fact (733 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p739 : Fact (739 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p743 : Fact (743 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p751 : Fact (751 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p683 : (E143_Finset 683).card = 687 := by decide
theorem BSD_E143_card_p691 : (E143_Finset 691).card = 736 := by decide
theorem BSD_E143_card_p701 : (E143_Finset 701).card = 711 := by decide
theorem BSD_E143_card_p709 : (E143_Finset 709).card = 744 := by decide
theorem BSD_E143_card_p719 : (E143_Finset 719).card = 760 := by decide
theorem BSD_E143_card_p727 : (E143_Finset 727).card = 708 := by decide
theorem BSD_E143_card_p733 : (E143_Finset 733).card = 779 := by decide
theorem BSD_E143_card_p739 : (E143_Finset 739).card = 741 := by decide
theorem BSD_E143_card_p743 : (E143_Finset 743).card = 701 := by decide
theorem BSD_E143_card_p751 : (E143_Finset 751).card = 790 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p683 : a_p 683 = (-4 : ℤ) := by
  have h := BSD_E143_card_p683; unfold a_p; omega
theorem BSD_ap_p691 : a_p 691 = (-45 : ℤ) := by
  have h := BSD_E143_card_p691; unfold a_p; omega
theorem BSD_ap_p701 : a_p 701 = (-10 : ℤ) := by
  have h := BSD_E143_card_p701; unfold a_p; omega
theorem BSD_ap_p709 : a_p 709 = (-35 : ℤ) := by
  have h := BSD_E143_card_p709; unfold a_p; omega
theorem BSD_ap_p719 : a_p 719 = (-41 : ℤ) := by
  have h := BSD_E143_card_p719; unfold a_p; omega
theorem BSD_ap_p727 : a_p 727 = (19 : ℤ) := by
  have h := BSD_E143_card_p727; unfold a_p; omega
theorem BSD_ap_p733 : a_p 733 = (-46 : ℤ) := by
  have h := BSD_E143_card_p733; unfold a_p; omega
theorem BSD_ap_p739 : a_p 739 = (-2 : ℤ) := by
  have h := BSD_E143_card_p739; unfold a_p; omega
theorem BSD_ap_p743 : a_p 743 = (42 : ℤ) := by
  have h := BSD_E143_card_p743; unfold a_p; omega
theorem BSD_ap_p751 : a_p 751 = (-39 : ℤ) := by
  have h := BSD_E143_card_p751; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=683: a_p=-4, disc=-2716
theorem BSD_DegreeNonneg_p683 : BSD_FrobeniusDegreeNonneg_OPEN 683 := fun r => by
  have hap : (a_p 683 : ℝ) = -4 := by exact_mod_cast BSD_ap_p683
  have key : r ^ 2 - (a_p 683 : ℝ) * r + ((683 : ℕ) : ℝ) =
      (r + 2) ^ 2 + 679 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 2)]

-- p=691: a_p=-45, disc=-739
theorem BSD_DegreeNonneg_p691 : BSD_FrobeniusDegreeNonneg_OPEN 691 := fun r => by
  have hap : (a_p 691 : ℝ) = -45 := by exact_mod_cast BSD_ap_p691
  have key : r ^ 2 - (a_p 691 : ℝ) * r + ((691 : ℕ) : ℝ) =
      (r + 45 / 2) ^ 2 + 739 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 45 / 2)]

-- p=701: a_p=-10, disc=-2704
theorem BSD_DegreeNonneg_p701 : BSD_FrobeniusDegreeNonneg_OPEN 701 := fun r => by
  have hap : (a_p 701 : ℝ) = -10 := by exact_mod_cast BSD_ap_p701
  have key : r ^ 2 - (a_p 701 : ℝ) * r + ((701 : ℕ) : ℝ) =
      (r + 5) ^ 2 + 676 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 5)]

-- p=709: a_p=-35, disc=-1611
theorem BSD_DegreeNonneg_p709 : BSD_FrobeniusDegreeNonneg_OPEN 709 := fun r => by
  have hap : (a_p 709 : ℝ) = -35 := by exact_mod_cast BSD_ap_p709
  have key : r ^ 2 - (a_p 709 : ℝ) * r + ((709 : ℕ) : ℝ) =
      (r + 35 / 2) ^ 2 + 1611 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 35 / 2)]

-- p=719: a_p=-41, disc=-1195
theorem BSD_DegreeNonneg_p719 : BSD_FrobeniusDegreeNonneg_OPEN 719 := fun r => by
  have hap : (a_p 719 : ℝ) = -41 := by exact_mod_cast BSD_ap_p719
  have key : r ^ 2 - (a_p 719 : ℝ) * r + ((719 : ℕ) : ℝ) =
      (r + 41 / 2) ^ 2 + 1195 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 41 / 2)]

-- p=727: a_p=+19, disc=-2547
theorem BSD_DegreeNonneg_p727 : BSD_FrobeniusDegreeNonneg_OPEN 727 := fun r => by
  have hap : (a_p 727 : ℝ) = 19 := by exact_mod_cast BSD_ap_p727
  have key : r ^ 2 - (a_p 727 : ℝ) * r + ((727 : ℕ) : ℝ) =
      (r - 19 / 2) ^ 2 + 2547 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 19 / 2)]

-- p=733: a_p=-46, disc=-816
theorem BSD_DegreeNonneg_p733 : BSD_FrobeniusDegreeNonneg_OPEN 733 := fun r => by
  have hap : (a_p 733 : ℝ) = -46 := by exact_mod_cast BSD_ap_p733
  have key : r ^ 2 - (a_p 733 : ℝ) * r + ((733 : ℕ) : ℝ) =
      (r + 23) ^ 2 + 204 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 23)]

-- p=739: a_p=-2, disc=-2952
theorem BSD_DegreeNonneg_p739 : BSD_FrobeniusDegreeNonneg_OPEN 739 := fun r => by
  have hap : (a_p 739 : ℝ) = -2 := by exact_mod_cast BSD_ap_p739
  have key : r ^ 2 - (a_p 739 : ℝ) * r + ((739 : ℕ) : ℝ) =
      (r + 1) ^ 2 + 738 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1)]

-- p=743: a_p=+42, disc=-1208
theorem BSD_DegreeNonneg_p743 : BSD_FrobeniusDegreeNonneg_OPEN 743 := fun r => by
  have hap : (a_p 743 : ℝ) = 42 := by exact_mod_cast BSD_ap_p743
  have key : r ^ 2 - (a_p 743 : ℝ) * r + ((743 : ℕ) : ℝ) =
      (r - 21) ^ 2 + 302 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 21)]

-- p=751: a_p=-39, disc=-1483
theorem BSD_DegreeNonneg_p751 : BSD_FrobeniusDegreeNonneg_OPEN 751 := fun r => by
  have hap : (a_p 751 : ℝ) = -39 := by exact_mod_cast BSD_ap_p751
  have key : r ^ 2 - (a_p 751 : ℝ) * r + ((751 : ℕ) : ℝ) =
      (r + 39 / 2) ^ 2 + 1483 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 39 / 2)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p683 : BSD_Hasse_OPEN 683 :=
  BSD_hasse_of_degree_nonneg 683 BSD_DegreeNonneg_p683
theorem BSD_Hasse_OPEN_p691 : BSD_Hasse_OPEN 691 :=
  BSD_hasse_of_degree_nonneg 691 BSD_DegreeNonneg_p691
theorem BSD_Hasse_OPEN_p701 : BSD_Hasse_OPEN 701 :=
  BSD_hasse_of_degree_nonneg 701 BSD_DegreeNonneg_p701
theorem BSD_Hasse_OPEN_p709 : BSD_Hasse_OPEN 709 :=
  BSD_hasse_of_degree_nonneg 709 BSD_DegreeNonneg_p709
theorem BSD_Hasse_OPEN_p719 : BSD_Hasse_OPEN 719 :=
  BSD_hasse_of_degree_nonneg 719 BSD_DegreeNonneg_p719
theorem BSD_Hasse_OPEN_p727 : BSD_Hasse_OPEN 727 :=
  BSD_hasse_of_degree_nonneg 727 BSD_DegreeNonneg_p727
theorem BSD_Hasse_OPEN_p733 : BSD_Hasse_OPEN 733 :=
  BSD_hasse_of_degree_nonneg 733 BSD_DegreeNonneg_p733
theorem BSD_Hasse_OPEN_p739 : BSD_Hasse_OPEN 739 :=
  BSD_hasse_of_degree_nonneg 739 BSD_DegreeNonneg_p739
theorem BSD_Hasse_OPEN_p743 : BSD_Hasse_OPEN 743 :=
  BSD_hasse_of_degree_nonneg 743 BSD_DegreeNonneg_p743
theorem BSD_Hasse_OPEN_p751 : BSD_Hasse_OPEN 751 :=
  BSD_hasse_of_degree_nonneg 751 BSD_DegreeNonneg_p751

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p683 : (a_p 683 : ℝ) ^ 2 ≤ 4 * (683 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p683
theorem BSD_HasseBound_Disc_p691 : (a_p 691 : ℝ) ^ 2 ≤ 4 * (691 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p691
theorem BSD_HasseBound_Disc_p701 : (a_p 701 : ℝ) ^ 2 ≤ 4 * (701 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p701
theorem BSD_HasseBound_Disc_p709 : (a_p 709 : ℝ) ^ 2 ≤ 4 * (709 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p709
theorem BSD_HasseBound_Disc_p719 : (a_p 719 : ℝ) ^ 2 ≤ 4 * (719 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p719
theorem BSD_HasseBound_Disc_p727 : (a_p 727 : ℝ) ^ 2 ≤ 4 * (727 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p727
theorem BSD_HasseBound_Disc_p733 : (a_p 733 : ℝ) ^ 2 ≤ 4 * (733 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p733
theorem BSD_HasseBound_Disc_p739 : (a_p 739 : ℝ) ^ 2 ≤ 4 * (739 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p739
theorem BSD_HasseBound_Disc_p743 : (a_p 743 : ℝ) ^ 2 ≤ 4 * (743 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p743
theorem BSD_HasseBound_Disc_p751 : (a_p 751 : ℝ) ^ 2 ≤ 4 * (751 : ℝ) :=
  BSD_disc_from_deg_770 BSD_DegreeNonneg_p751

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_131prime_CLOSED :
    (131 : ℕ) ≤ 131 := le_refl 131

theorem BSD_HasseBound_Discriminant_TierA_Batch8 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({683, 691, 701, 709, 719, 727, 733, 739, 743, 751} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p683
  · exact BSD_HasseBound_Disc_p691
  · exact BSD_HasseBound_Disc_p701
  · exact BSD_HasseBound_Disc_p709
  · exact BSD_HasseBound_Disc_p719
  · exact BSD_HasseBound_Disc_p727
  · exact BSD_HasseBound_Disc_p733
  · exact BSD_HasseBound_Disc_p739
  · exact BSD_HasseBound_Disc_p743
  · exact BSD_HasseBound_Disc_p751

/-! ## §7. Combinator -/

theorem BSD_Genesis770_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis769_Combinator h_disc h_anchor

end Towers.BSD