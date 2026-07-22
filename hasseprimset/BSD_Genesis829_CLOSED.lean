/-
================================================================
Towers / BSD / BSD_Genesis829_CLOSED  (genesis-829)

HasseBridge Tier C: Hasse bounds for primes
4651..4729 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4651: card=4645, a_p=+7, disc=-18555
  p=4657: card=4617, a_p=+41, disc=-16947
  p=4663: card=4668, a_p=-4, disc=-18636
  p=4673: card=4768, a_p=-94, disc=-9856
  p=4679: card=4767, a_p=-87, disc=-11147
  p=4691: card=4697, a_p=-5, disc=-18739
  p=4703: card=4692, a_p=+12, disc=-18668
  p=4721: card=4634, a_p=+88, disc=-11140
  p=4723: card=4800, a_p=-76, disc=-13116
  p=4729: card=4620, a_p=+110, disc=-6816

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_829 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i829_p4651 : Fact (4651 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4657 : Fact (4657 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4663 : Fact (4663 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4673 : Fact (4673 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4679 : Fact (4679 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4691 : Fact (4691 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4703 : Fact (4703 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4721 : Fact (4721 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4723 : Fact (4723 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4729 : Fact (4729 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4651 : (E143_Finset 4651).card = 4645 := by native_decide
theorem BSD_E143_card_p4657 : (E143_Finset 4657).card = 4617 := by native_decide
theorem BSD_E143_card_p4663 : (E143_Finset 4663).card = 4668 := by native_decide
theorem BSD_E143_card_p4673 : (E143_Finset 4673).card = 4768 := by native_decide
theorem BSD_E143_card_p4679 : (E143_Finset 4679).card = 4767 := by native_decide
theorem BSD_E143_card_p4691 : (E143_Finset 4691).card = 4697 := by native_decide
theorem BSD_E143_card_p4703 : (E143_Finset 4703).card = 4692 := by native_decide
theorem BSD_E143_card_p4721 : (E143_Finset 4721).card = 4634 := by native_decide
theorem BSD_E143_card_p4723 : (E143_Finset 4723).card = 4800 := by native_decide
theorem BSD_E143_card_p4729 : (E143_Finset 4729).card = 4620 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4651 : a_p 4651 = (7 : ℤ) := by
  have h := BSD_E143_card_p4651; unfold a_p; omega
theorem BSD_ap_p4657 : a_p 4657 = (41 : ℤ) := by
  have h := BSD_E143_card_p4657; unfold a_p; omega
theorem BSD_ap_p4663 : a_p 4663 = (-4 : ℤ) := by
  have h := BSD_E143_card_p4663; unfold a_p; omega
theorem BSD_ap_p4673 : a_p 4673 = (-94 : ℤ) := by
  have h := BSD_E143_card_p4673; unfold a_p; omega
theorem BSD_ap_p4679 : a_p 4679 = (-87 : ℤ) := by
  have h := BSD_E143_card_p4679; unfold a_p; omega
theorem BSD_ap_p4691 : a_p 4691 = (-5 : ℤ) := by
  have h := BSD_E143_card_p4691; unfold a_p; omega
theorem BSD_ap_p4703 : a_p 4703 = (12 : ℤ) := by
  have h := BSD_E143_card_p4703; unfold a_p; omega
theorem BSD_ap_p4721 : a_p 4721 = (88 : ℤ) := by
  have h := BSD_E143_card_p4721; unfold a_p; omega
theorem BSD_ap_p4723 : a_p 4723 = (-76 : ℤ) := by
  have h := BSD_E143_card_p4723; unfold a_p; omega
theorem BSD_ap_p4729 : a_p 4729 = (110 : ℤ) := by
  have h := BSD_E143_card_p4729; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4651: a_p=+7, 4p-a_p²=18555
theorem BSD_DegreeNonneg_p4651 : BSD_FrobeniusDegreeNonneg_OPEN 4651 := fun r => by
  have hap : (a_p 4651 : ℝ) = 7 := by exact_mod_cast BSD_ap_p4651
  have key : r ^ 2 - (a_p 4651 : ℝ) * r + ((4651 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 18555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

-- p=4657: a_p=+41, 4p-a_p²=16947
theorem BSD_DegreeNonneg_p4657 : BSD_FrobeniusDegreeNonneg_OPEN 4657 := fun r => by
  have hap : (a_p 4657 : ℝ) = 41 := by exact_mod_cast BSD_ap_p4657
  have key : r ^ 2 - (a_p 4657 : ℝ) * r + ((4657 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 16947/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

-- p=4663: a_p=-4, 4p-a_p²=18636
theorem BSD_DegreeNonneg_p4663 : BSD_FrobeniusDegreeNonneg_OPEN 4663 := fun r => by
  have hap : (a_p 4663 : ℝ) = -4 := by exact_mod_cast BSD_ap_p4663
  have key : r ^ 2 - (a_p 4663 : ℝ) * r + ((4663 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 18636/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

-- p=4673: a_p=-94, 4p-a_p²=9856
theorem BSD_DegreeNonneg_p4673 : BSD_FrobeniusDegreeNonneg_OPEN 4673 := fun r => by
  have hap : (a_p 4673 : ℝ) = -94 := by exact_mod_cast BSD_ap_p4673
  have key : r ^ 2 - (a_p 4673 : ℝ) * r + ((4673 : ℕ) : ℝ) =
      (r + 94/2) ^ 2 + 9856/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (94 : ℝ)/2)]

-- p=4679: a_p=-87, 4p-a_p²=11147
theorem BSD_DegreeNonneg_p4679 : BSD_FrobeniusDegreeNonneg_OPEN 4679 := fun r => by
  have hap : (a_p 4679 : ℝ) = -87 := by exact_mod_cast BSD_ap_p4679
  have key : r ^ 2 - (a_p 4679 : ℝ) * r + ((4679 : ℕ) : ℝ) =
      (r + 87/2) ^ 2 + 11147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (87 : ℝ)/2)]

-- p=4691: a_p=-5, 4p-a_p²=18739
theorem BSD_DegreeNonneg_p4691 : BSD_FrobeniusDegreeNonneg_OPEN 4691 := fun r => by
  have hap : (a_p 4691 : ℝ) = -5 := by exact_mod_cast BSD_ap_p4691
  have key : r ^ 2 - (a_p 4691 : ℝ) * r + ((4691 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 18739/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

-- p=4703: a_p=+12, 4p-a_p²=18668
theorem BSD_DegreeNonneg_p4703 : BSD_FrobeniusDegreeNonneg_OPEN 4703 := fun r => by
  have hap : (a_p 4703 : ℝ) = 12 := by exact_mod_cast BSD_ap_p4703
  have key : r ^ 2 - (a_p 4703 : ℝ) * r + ((4703 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 18668/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=4721: a_p=+88, 4p-a_p²=11140
theorem BSD_DegreeNonneg_p4721 : BSD_FrobeniusDegreeNonneg_OPEN 4721 := fun r => by
  have hap : (a_p 4721 : ℝ) = 88 := by exact_mod_cast BSD_ap_p4721
  have key : r ^ 2 - (a_p 4721 : ℝ) * r + ((4721 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 11140/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

-- p=4723: a_p=-76, 4p-a_p²=13116
theorem BSD_DegreeNonneg_p4723 : BSD_FrobeniusDegreeNonneg_OPEN 4723 := fun r => by
  have hap : (a_p 4723 : ℝ) = -76 := by exact_mod_cast BSD_ap_p4723
  have key : r ^ 2 - (a_p 4723 : ℝ) * r + ((4723 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 13116/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

-- p=4729: a_p=+110, 4p-a_p²=6816
theorem BSD_DegreeNonneg_p4729 : BSD_FrobeniusDegreeNonneg_OPEN 4729 := fun r => by
  have hap : (a_p 4729 : ℝ) = 110 := by exact_mod_cast BSD_ap_p4729
  have key : r ^ 2 - (a_p 4729 : ℝ) * r + ((4729 : ℕ) : ℝ) =
      (r - 110/2) ^ 2 + 6816/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (110 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4651 : BSD_Hasse_OPEN 4651 :=
  BSD_hasse_of_degree_nonneg 4651 BSD_DegreeNonneg_p4651
theorem BSD_Hasse_OPEN_p4657 : BSD_Hasse_OPEN 4657 :=
  BSD_hasse_of_degree_nonneg 4657 BSD_DegreeNonneg_p4657
theorem BSD_Hasse_OPEN_p4663 : BSD_Hasse_OPEN 4663 :=
  BSD_hasse_of_degree_nonneg 4663 BSD_DegreeNonneg_p4663
theorem BSD_Hasse_OPEN_p4673 : BSD_Hasse_OPEN 4673 :=
  BSD_hasse_of_degree_nonneg 4673 BSD_DegreeNonneg_p4673
theorem BSD_Hasse_OPEN_p4679 : BSD_Hasse_OPEN 4679 :=
  BSD_hasse_of_degree_nonneg 4679 BSD_DegreeNonneg_p4679
theorem BSD_Hasse_OPEN_p4691 : BSD_Hasse_OPEN 4691 :=
  BSD_hasse_of_degree_nonneg 4691 BSD_DegreeNonneg_p4691
theorem BSD_Hasse_OPEN_p4703 : BSD_Hasse_OPEN 4703 :=
  BSD_hasse_of_degree_nonneg 4703 BSD_DegreeNonneg_p4703
theorem BSD_Hasse_OPEN_p4721 : BSD_Hasse_OPEN 4721 :=
  BSD_hasse_of_degree_nonneg 4721 BSD_DegreeNonneg_p4721
theorem BSD_Hasse_OPEN_p4723 : BSD_Hasse_OPEN 4723 :=
  BSD_hasse_of_degree_nonneg 4723 BSD_DegreeNonneg_p4723
theorem BSD_Hasse_OPEN_p4729 : BSD_Hasse_OPEN 4729 :=
  BSD_hasse_of_degree_nonneg 4729 BSD_DegreeNonneg_p4729

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4651 : (a_p 4651 : ℝ) ^ 2 ≤ 4 * (4651 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4651
theorem BSD_HasseBound_Disc_p4657 : (a_p 4657 : ℝ) ^ 2 ≤ 4 * (4657 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4657
theorem BSD_HasseBound_Disc_p4663 : (a_p 4663 : ℝ) ^ 2 ≤ 4 * (4663 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4663
theorem BSD_HasseBound_Disc_p4673 : (a_p 4673 : ℝ) ^ 2 ≤ 4 * (4673 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4673
theorem BSD_HasseBound_Disc_p4679 : (a_p 4679 : ℝ) ^ 2 ≤ 4 * (4679 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4679
theorem BSD_HasseBound_Disc_p4691 : (a_p 4691 : ℝ) ^ 2 ≤ 4 * (4691 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4691
theorem BSD_HasseBound_Disc_p4703 : (a_p 4703 : ℝ) ^ 2 ≤ 4 * (4703 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4703
theorem BSD_HasseBound_Disc_p4721 : (a_p 4721 : ℝ) ^ 2 ≤ 4 * (4721 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4721
theorem BSD_HasseBound_Disc_p4723 : (a_p 4723 : ℝ) ^ 2 ≤ 4 * (4723 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4723
theorem BSD_HasseBound_Disc_p4729 : (a_p 4729 : ℝ) ^ 2 ≤ 4 * (4729 : ℝ) :=
  BSD_disc_from_deg_829 BSD_DegreeNonneg_p4729

end Towers.BSD