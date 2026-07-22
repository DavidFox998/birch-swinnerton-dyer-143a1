/-
================================================================
Towers / BSD / BSD_Genesis875_CLOSED  (genesis-875)

HasseBridge Tier C: Hasse bounds for primes
8737..8819 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8737: card=8828, a_p=-90, disc=-26848
  p=8741: card=8718, a_p=+24, disc=-34388
  p=8747: card=8918, a_p=-170, disc=-6088
  p=8753: card=8716, a_p=+38, disc=-33568
  p=8761: card=8831, a_p=-69, disc=-30283
  p=8779: card=8845, a_p=-65, disc=-30891
  p=8783: card=8841, a_p=-57, disc=-31883
  p=8803: card=8712, a_p=+92, disc=-26748
  p=8807: card=8684, a_p=+124, disc=-19852
  p=8819: card=8874, a_p=-54, disc=-32360

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_875 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i875_p8737 : Fact (8737 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8741 : Fact (8741 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8747 : Fact (8747 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8753 : Fact (8753 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8761 : Fact (8761 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8779 : Fact (8779 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8783 : Fact (8783 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8803 : Fact (8803 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8807 : Fact (8807 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8819 : Fact (8819 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8737 : (E143_Finset 8737).card = 8828 := by native_decide
theorem BSD_E143_card_p8741 : (E143_Finset 8741).card = 8718 := by native_decide
theorem BSD_E143_card_p8747 : (E143_Finset 8747).card = 8918 := by native_decide
theorem BSD_E143_card_p8753 : (E143_Finset 8753).card = 8716 := by native_decide
theorem BSD_E143_card_p8761 : (E143_Finset 8761).card = 8831 := by native_decide
theorem BSD_E143_card_p8779 : (E143_Finset 8779).card = 8845 := by native_decide
theorem BSD_E143_card_p8783 : (E143_Finset 8783).card = 8841 := by native_decide
theorem BSD_E143_card_p8803 : (E143_Finset 8803).card = 8712 := by native_decide
theorem BSD_E143_card_p8807 : (E143_Finset 8807).card = 8684 := by native_decide
theorem BSD_E143_card_p8819 : (E143_Finset 8819).card = 8874 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8737 : a_p 8737 = (-90 : ℤ) := by
  have h := BSD_E143_card_p8737; unfold a_p; omega
theorem BSD_ap_p8741 : a_p 8741 = (24 : ℤ) := by
  have h := BSD_E143_card_p8741; unfold a_p; omega
theorem BSD_ap_p8747 : a_p 8747 = (-170 : ℤ) := by
  have h := BSD_E143_card_p8747; unfold a_p; omega
theorem BSD_ap_p8753 : a_p 8753 = (38 : ℤ) := by
  have h := BSD_E143_card_p8753; unfold a_p; omega
theorem BSD_ap_p8761 : a_p 8761 = (-69 : ℤ) := by
  have h := BSD_E143_card_p8761; unfold a_p; omega
theorem BSD_ap_p8779 : a_p 8779 = (-65 : ℤ) := by
  have h := BSD_E143_card_p8779; unfold a_p; omega
theorem BSD_ap_p8783 : a_p 8783 = (-57 : ℤ) := by
  have h := BSD_E143_card_p8783; unfold a_p; omega
theorem BSD_ap_p8803 : a_p 8803 = (92 : ℤ) := by
  have h := BSD_E143_card_p8803; unfold a_p; omega
theorem BSD_ap_p8807 : a_p 8807 = (124 : ℤ) := by
  have h := BSD_E143_card_p8807; unfold a_p; omega
theorem BSD_ap_p8819 : a_p 8819 = (-54 : ℤ) := by
  have h := BSD_E143_card_p8819; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8737: a_p=-90, 4p-a_p²=26848
theorem BSD_DegreeNonneg_p8737 : BSD_FrobeniusDegreeNonneg_OPEN 8737 := fun r => by
  have hap : (a_p 8737 : ℝ) = -90 := by exact_mod_cast BSD_ap_p8737
  have key : r ^ 2 - (a_p 8737 : ℝ) * r + ((8737 : ℕ) : ℝ) =
      (r + 90/2) ^ 2 + 26848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (90 : ℝ)/2)]

-- p=8741: a_p=+24, 4p-a_p²=34388
theorem BSD_DegreeNonneg_p8741 : BSD_FrobeniusDegreeNonneg_OPEN 8741 := fun r => by
  have hap : (a_p 8741 : ℝ) = 24 := by exact_mod_cast BSD_ap_p8741
  have key : r ^ 2 - (a_p 8741 : ℝ) * r + ((8741 : ℕ) : ℝ) =
      (r - 24/2) ^ 2 + 34388/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (24 : ℝ)/2)]

-- p=8747: a_p=-170, 4p-a_p²=6088
theorem BSD_DegreeNonneg_p8747 : BSD_FrobeniusDegreeNonneg_OPEN 8747 := fun r => by
  have hap : (a_p 8747 : ℝ) = -170 := by exact_mod_cast BSD_ap_p8747
  have key : r ^ 2 - (a_p 8747 : ℝ) * r + ((8747 : ℕ) : ℝ) =
      (r + 170/2) ^ 2 + 6088/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (170 : ℝ)/2)]

-- p=8753: a_p=+38, 4p-a_p²=33568
theorem BSD_DegreeNonneg_p8753 : BSD_FrobeniusDegreeNonneg_OPEN 8753 := fun r => by
  have hap : (a_p 8753 : ℝ) = 38 := by exact_mod_cast BSD_ap_p8753
  have key : r ^ 2 - (a_p 8753 : ℝ) * r + ((8753 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 33568/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

-- p=8761: a_p=-69, 4p-a_p²=30283
theorem BSD_DegreeNonneg_p8761 : BSD_FrobeniusDegreeNonneg_OPEN 8761 := fun r => by
  have hap : (a_p 8761 : ℝ) = -69 := by exact_mod_cast BSD_ap_p8761
  have key : r ^ 2 - (a_p 8761 : ℝ) * r + ((8761 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 30283/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

-- p=8779: a_p=-65, 4p-a_p²=30891
theorem BSD_DegreeNonneg_p8779 : BSD_FrobeniusDegreeNonneg_OPEN 8779 := fun r => by
  have hap : (a_p 8779 : ℝ) = -65 := by exact_mod_cast BSD_ap_p8779
  have key : r ^ 2 - (a_p 8779 : ℝ) * r + ((8779 : ℕ) : ℝ) =
      (r + 65/2) ^ 2 + 30891/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (65 : ℝ)/2)]

-- p=8783: a_p=-57, 4p-a_p²=31883
theorem BSD_DegreeNonneg_p8783 : BSD_FrobeniusDegreeNonneg_OPEN 8783 := fun r => by
  have hap : (a_p 8783 : ℝ) = -57 := by exact_mod_cast BSD_ap_p8783
  have key : r ^ 2 - (a_p 8783 : ℝ) * r + ((8783 : ℕ) : ℝ) =
      (r + 57/2) ^ 2 + 31883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (57 : ℝ)/2)]

-- p=8803: a_p=+92, 4p-a_p²=26748
theorem BSD_DegreeNonneg_p8803 : BSD_FrobeniusDegreeNonneg_OPEN 8803 := fun r => by
  have hap : (a_p 8803 : ℝ) = 92 := by exact_mod_cast BSD_ap_p8803
  have key : r ^ 2 - (a_p 8803 : ℝ) * r + ((8803 : ℕ) : ℝ) =
      (r - 92/2) ^ 2 + 26748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (92 : ℝ)/2)]

-- p=8807: a_p=+124, 4p-a_p²=19852
theorem BSD_DegreeNonneg_p8807 : BSD_FrobeniusDegreeNonneg_OPEN 8807 := fun r => by
  have hap : (a_p 8807 : ℝ) = 124 := by exact_mod_cast BSD_ap_p8807
  have key : r ^ 2 - (a_p 8807 : ℝ) * r + ((8807 : ℕ) : ℝ) =
      (r - 124/2) ^ 2 + 19852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (124 : ℝ)/2)]

-- p=8819: a_p=-54, 4p-a_p²=32360
theorem BSD_DegreeNonneg_p8819 : BSD_FrobeniusDegreeNonneg_OPEN 8819 := fun r => by
  have hap : (a_p 8819 : ℝ) = -54 := by exact_mod_cast BSD_ap_p8819
  have key : r ^ 2 - (a_p 8819 : ℝ) * r + ((8819 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 32360/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8737 : BSD_Hasse_OPEN 8737 :=
  BSD_hasse_of_degree_nonneg 8737 BSD_DegreeNonneg_p8737
theorem BSD_Hasse_OPEN_p8741 : BSD_Hasse_OPEN 8741 :=
  BSD_hasse_of_degree_nonneg 8741 BSD_DegreeNonneg_p8741
theorem BSD_Hasse_OPEN_p8747 : BSD_Hasse_OPEN 8747 :=
  BSD_hasse_of_degree_nonneg 8747 BSD_DegreeNonneg_p8747
theorem BSD_Hasse_OPEN_p8753 : BSD_Hasse_OPEN 8753 :=
  BSD_hasse_of_degree_nonneg 8753 BSD_DegreeNonneg_p8753
theorem BSD_Hasse_OPEN_p8761 : BSD_Hasse_OPEN 8761 :=
  BSD_hasse_of_degree_nonneg 8761 BSD_DegreeNonneg_p8761
theorem BSD_Hasse_OPEN_p8779 : BSD_Hasse_OPEN 8779 :=
  BSD_hasse_of_degree_nonneg 8779 BSD_DegreeNonneg_p8779
theorem BSD_Hasse_OPEN_p8783 : BSD_Hasse_OPEN 8783 :=
  BSD_hasse_of_degree_nonneg 8783 BSD_DegreeNonneg_p8783
theorem BSD_Hasse_OPEN_p8803 : BSD_Hasse_OPEN 8803 :=
  BSD_hasse_of_degree_nonneg 8803 BSD_DegreeNonneg_p8803
theorem BSD_Hasse_OPEN_p8807 : BSD_Hasse_OPEN 8807 :=
  BSD_hasse_of_degree_nonneg 8807 BSD_DegreeNonneg_p8807
theorem BSD_Hasse_OPEN_p8819 : BSD_Hasse_OPEN 8819 :=
  BSD_hasse_of_degree_nonneg 8819 BSD_DegreeNonneg_p8819

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8737 : (a_p 8737 : ℝ) ^ 2 ≤ 4 * (8737 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8737
theorem BSD_HasseBound_Disc_p8741 : (a_p 8741 : ℝ) ^ 2 ≤ 4 * (8741 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8741
theorem BSD_HasseBound_Disc_p8747 : (a_p 8747 : ℝ) ^ 2 ≤ 4 * (8747 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8747
theorem BSD_HasseBound_Disc_p8753 : (a_p 8753 : ℝ) ^ 2 ≤ 4 * (8753 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8753
theorem BSD_HasseBound_Disc_p8761 : (a_p 8761 : ℝ) ^ 2 ≤ 4 * (8761 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8761
theorem BSD_HasseBound_Disc_p8779 : (a_p 8779 : ℝ) ^ 2 ≤ 4 * (8779 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8779
theorem BSD_HasseBound_Disc_p8783 : (a_p 8783 : ℝ) ^ 2 ≤ 4 * (8783 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8783
theorem BSD_HasseBound_Disc_p8803 : (a_p 8803 : ℝ) ^ 2 ≤ 4 * (8803 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8803
theorem BSD_HasseBound_Disc_p8807 : (a_p 8807 : ℝ) ^ 2 ≤ 4 * (8807 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8807
theorem BSD_HasseBound_Disc_p8819 : (a_p 8819 : ℝ) ^ 2 ≤ 4 * (8819 : ℝ) :=
  BSD_disc_from_deg_875 BSD_DegreeNonneg_p8819

end Towers.BSD