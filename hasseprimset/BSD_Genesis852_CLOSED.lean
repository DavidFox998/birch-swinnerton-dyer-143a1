/-
================================================================
Towers / BSD / BSD_Genesis852_CLOSED  (genesis-852)

HasseBridge Tier C: Hasse bounds for primes
6661..6733 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6661: card=6552, a_p=+110, disc=-14544
  p=6673: card=6830, a_p=-156, disc=-2356
  p=6679: card=6798, a_p=-118, disc=-12792
  p=6689: card=6581, a_p=+109, disc=-14875
  p=6691: card=6679, a_p=+13, disc=-26595
  p=6701: card=6662, a_p=+40, disc=-25204
  p=6703: card=6633, a_p=+71, disc=-21771
  p=6709: card=6588, a_p=+122, disc=-11952
  p=6719: card=6588, a_p=+132, disc=-9452
  p=6733: card=6597, a_p=+137, disc=-8163

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_852 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i852_p6661 : Fact (6661 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6673 : Fact (6673 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6679 : Fact (6679 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6689 : Fact (6689 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6691 : Fact (6691 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6701 : Fact (6701 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6703 : Fact (6703 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6709 : Fact (6709 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6719 : Fact (6719 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6733 : Fact (6733 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6661 : (E143_Finset 6661).card = 6552 := by native_decide
theorem BSD_E143_card_p6673 : (E143_Finset 6673).card = 6830 := by native_decide
theorem BSD_E143_card_p6679 : (E143_Finset 6679).card = 6798 := by native_decide
theorem BSD_E143_card_p6689 : (E143_Finset 6689).card = 6581 := by native_decide
theorem BSD_E143_card_p6691 : (E143_Finset 6691).card = 6679 := by native_decide
theorem BSD_E143_card_p6701 : (E143_Finset 6701).card = 6662 := by native_decide
theorem BSD_E143_card_p6703 : (E143_Finset 6703).card = 6633 := by native_decide
theorem BSD_E143_card_p6709 : (E143_Finset 6709).card = 6588 := by native_decide
theorem BSD_E143_card_p6719 : (E143_Finset 6719).card = 6588 := by native_decide
theorem BSD_E143_card_p6733 : (E143_Finset 6733).card = 6597 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6661 : a_p 6661 = (110 : ℤ) := by
  have h := BSD_E143_card_p6661; unfold a_p; omega
theorem BSD_ap_p6673 : a_p 6673 = (-156 : ℤ) := by
  have h := BSD_E143_card_p6673; unfold a_p; omega
theorem BSD_ap_p6679 : a_p 6679 = (-118 : ℤ) := by
  have h := BSD_E143_card_p6679; unfold a_p; omega
theorem BSD_ap_p6689 : a_p 6689 = (109 : ℤ) := by
  have h := BSD_E143_card_p6689; unfold a_p; omega
theorem BSD_ap_p6691 : a_p 6691 = (13 : ℤ) := by
  have h := BSD_E143_card_p6691; unfold a_p; omega
theorem BSD_ap_p6701 : a_p 6701 = (40 : ℤ) := by
  have h := BSD_E143_card_p6701; unfold a_p; omega
theorem BSD_ap_p6703 : a_p 6703 = (71 : ℤ) := by
  have h := BSD_E143_card_p6703; unfold a_p; omega
theorem BSD_ap_p6709 : a_p 6709 = (122 : ℤ) := by
  have h := BSD_E143_card_p6709; unfold a_p; omega
theorem BSD_ap_p6719 : a_p 6719 = (132 : ℤ) := by
  have h := BSD_E143_card_p6719; unfold a_p; omega
theorem BSD_ap_p6733 : a_p 6733 = (137 : ℤ) := by
  have h := BSD_E143_card_p6733; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6661: a_p=+110, 4p-a_p²=14544
theorem BSD_DegreeNonneg_p6661 : BSD_FrobeniusDegreeNonneg_OPEN 6661 := fun r => by
  have hap : (a_p 6661 : ℝ) = 110 := by exact_mod_cast BSD_ap_p6661
  have key : r ^ 2 - (a_p 6661 : ℝ) * r + ((6661 : ℕ) : ℝ) =
      (r - 110/2) ^ 2 + 14544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (110 : ℝ)/2)]

-- p=6673: a_p=-156, 4p-a_p²=2356
theorem BSD_DegreeNonneg_p6673 : BSD_FrobeniusDegreeNonneg_OPEN 6673 := fun r => by
  have hap : (a_p 6673 : ℝ) = -156 := by exact_mod_cast BSD_ap_p6673
  have key : r ^ 2 - (a_p 6673 : ℝ) * r + ((6673 : ℕ) : ℝ) =
      (r + 156/2) ^ 2 + 2356/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (156 : ℝ)/2)]

-- p=6679: a_p=-118, 4p-a_p²=12792
theorem BSD_DegreeNonneg_p6679 : BSD_FrobeniusDegreeNonneg_OPEN 6679 := fun r => by
  have hap : (a_p 6679 : ℝ) = -118 := by exact_mod_cast BSD_ap_p6679
  have key : r ^ 2 - (a_p 6679 : ℝ) * r + ((6679 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 12792/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

-- p=6689: a_p=+109, 4p-a_p²=14875
theorem BSD_DegreeNonneg_p6689 : BSD_FrobeniusDegreeNonneg_OPEN 6689 := fun r => by
  have hap : (a_p 6689 : ℝ) = 109 := by exact_mod_cast BSD_ap_p6689
  have key : r ^ 2 - (a_p 6689 : ℝ) * r + ((6689 : ℕ) : ℝ) =
      (r - 109/2) ^ 2 + 14875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (109 : ℝ)/2)]

-- p=6691: a_p=+13, 4p-a_p²=26595
theorem BSD_DegreeNonneg_p6691 : BSD_FrobeniusDegreeNonneg_OPEN 6691 := fun r => by
  have hap : (a_p 6691 : ℝ) = 13 := by exact_mod_cast BSD_ap_p6691
  have key : r ^ 2 - (a_p 6691 : ℝ) * r + ((6691 : ℕ) : ℝ) =
      (r - 13/2) ^ 2 + 26595/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (13 : ℝ)/2)]

-- p=6701: a_p=+40, 4p-a_p²=25204
theorem BSD_DegreeNonneg_p6701 : BSD_FrobeniusDegreeNonneg_OPEN 6701 := fun r => by
  have hap : (a_p 6701 : ℝ) = 40 := by exact_mod_cast BSD_ap_p6701
  have key : r ^ 2 - (a_p 6701 : ℝ) * r + ((6701 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 25204/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

-- p=6703: a_p=+71, 4p-a_p²=21771
theorem BSD_DegreeNonneg_p6703 : BSD_FrobeniusDegreeNonneg_OPEN 6703 := fun r => by
  have hap : (a_p 6703 : ℝ) = 71 := by exact_mod_cast BSD_ap_p6703
  have key : r ^ 2 - (a_p 6703 : ℝ) * r + ((6703 : ℕ) : ℝ) =
      (r - 71/2) ^ 2 + 21771/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (71 : ℝ)/2)]

-- p=6709: a_p=+122, 4p-a_p²=11952
theorem BSD_DegreeNonneg_p6709 : BSD_FrobeniusDegreeNonneg_OPEN 6709 := fun r => by
  have hap : (a_p 6709 : ℝ) = 122 := by exact_mod_cast BSD_ap_p6709
  have key : r ^ 2 - (a_p 6709 : ℝ) * r + ((6709 : ℕ) : ℝ) =
      (r - 122/2) ^ 2 + 11952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (122 : ℝ)/2)]

-- p=6719: a_p=+132, 4p-a_p²=9452
theorem BSD_DegreeNonneg_p6719 : BSD_FrobeniusDegreeNonneg_OPEN 6719 := fun r => by
  have hap : (a_p 6719 : ℝ) = 132 := by exact_mod_cast BSD_ap_p6719
  have key : r ^ 2 - (a_p 6719 : ℝ) * r + ((6719 : ℕ) : ℝ) =
      (r - 132/2) ^ 2 + 9452/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (132 : ℝ)/2)]

-- p=6733: a_p=+137, 4p-a_p²=8163
theorem BSD_DegreeNonneg_p6733 : BSD_FrobeniusDegreeNonneg_OPEN 6733 := fun r => by
  have hap : (a_p 6733 : ℝ) = 137 := by exact_mod_cast BSD_ap_p6733
  have key : r ^ 2 - (a_p 6733 : ℝ) * r + ((6733 : ℕ) : ℝ) =
      (r - 137/2) ^ 2 + 8163/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (137 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6661 : BSD_Hasse_OPEN 6661 :=
  BSD_hasse_of_degree_nonneg 6661 BSD_DegreeNonneg_p6661
theorem BSD_Hasse_OPEN_p6673 : BSD_Hasse_OPEN 6673 :=
  BSD_hasse_of_degree_nonneg 6673 BSD_DegreeNonneg_p6673
theorem BSD_Hasse_OPEN_p6679 : BSD_Hasse_OPEN 6679 :=
  BSD_hasse_of_degree_nonneg 6679 BSD_DegreeNonneg_p6679
theorem BSD_Hasse_OPEN_p6689 : BSD_Hasse_OPEN 6689 :=
  BSD_hasse_of_degree_nonneg 6689 BSD_DegreeNonneg_p6689
theorem BSD_Hasse_OPEN_p6691 : BSD_Hasse_OPEN 6691 :=
  BSD_hasse_of_degree_nonneg 6691 BSD_DegreeNonneg_p6691
theorem BSD_Hasse_OPEN_p6701 : BSD_Hasse_OPEN 6701 :=
  BSD_hasse_of_degree_nonneg 6701 BSD_DegreeNonneg_p6701
theorem BSD_Hasse_OPEN_p6703 : BSD_Hasse_OPEN 6703 :=
  BSD_hasse_of_degree_nonneg 6703 BSD_DegreeNonneg_p6703
theorem BSD_Hasse_OPEN_p6709 : BSD_Hasse_OPEN 6709 :=
  BSD_hasse_of_degree_nonneg 6709 BSD_DegreeNonneg_p6709
theorem BSD_Hasse_OPEN_p6719 : BSD_Hasse_OPEN 6719 :=
  BSD_hasse_of_degree_nonneg 6719 BSD_DegreeNonneg_p6719
theorem BSD_Hasse_OPEN_p6733 : BSD_Hasse_OPEN 6733 :=
  BSD_hasse_of_degree_nonneg 6733 BSD_DegreeNonneg_p6733

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6661 : (a_p 6661 : ℝ) ^ 2 ≤ 4 * (6661 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6661
theorem BSD_HasseBound_Disc_p6673 : (a_p 6673 : ℝ) ^ 2 ≤ 4 * (6673 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6673
theorem BSD_HasseBound_Disc_p6679 : (a_p 6679 : ℝ) ^ 2 ≤ 4 * (6679 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6679
theorem BSD_HasseBound_Disc_p6689 : (a_p 6689 : ℝ) ^ 2 ≤ 4 * (6689 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6689
theorem BSD_HasseBound_Disc_p6691 : (a_p 6691 : ℝ) ^ 2 ≤ 4 * (6691 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6691
theorem BSD_HasseBound_Disc_p6701 : (a_p 6701 : ℝ) ^ 2 ≤ 4 * (6701 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6701
theorem BSD_HasseBound_Disc_p6703 : (a_p 6703 : ℝ) ^ 2 ≤ 4 * (6703 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6703
theorem BSD_HasseBound_Disc_p6709 : (a_p 6709 : ℝ) ^ 2 ≤ 4 * (6709 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6709
theorem BSD_HasseBound_Disc_p6719 : (a_p 6719 : ℝ) ^ 2 ≤ 4 * (6719 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6719
theorem BSD_HasseBound_Disc_p6733 : (a_p 6733 : ℝ) ^ 2 ≤ 4 * (6733 : ℝ) :=
  BSD_disc_from_deg_852 BSD_DegreeNonneg_p6733

end Towers.BSD