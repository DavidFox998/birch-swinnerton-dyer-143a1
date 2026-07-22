/-
================================================================
Towers / BSD / BSD_Genesis850_CLOSED  (genesis-850)

HasseBridge Tier C: Hasse bounds for primes
6469..6563 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6469: card=6439, a_p=+31, disc=-24915
  p=6473: card=6441, a_p=+33, disc=-24803
  p=6481: card=6336, a_p=+146, disc=-4608
  p=6491: card=6567, a_p=-75, disc=-20339
  p=6521: card=6531, a_p=-9, disc=-26003
  p=6529: card=6544, a_p=-14, disc=-25920
  p=6547: card=6606, a_p=-58, disc=-22824
  p=6551: card=6638, a_p=-86, disc=-18808
  p=6553: card=6574, a_p=-20, disc=-25812
  p=6563: card=6464, a_p=+100, disc=-16252

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_850 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i850_p6469 : Fact (6469 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6473 : Fact (6473 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6481 : Fact (6481 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6491 : Fact (6491 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6521 : Fact (6521 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6529 : Fact (6529 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6547 : Fact (6547 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6551 : Fact (6551 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6553 : Fact (6553 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6563 : Fact (6563 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6469 : (E143_Finset 6469).card = 6439 := by native_decide
theorem BSD_E143_card_p6473 : (E143_Finset 6473).card = 6441 := by native_decide
theorem BSD_E143_card_p6481 : (E143_Finset 6481).card = 6336 := by native_decide
theorem BSD_E143_card_p6491 : (E143_Finset 6491).card = 6567 := by native_decide
theorem BSD_E143_card_p6521 : (E143_Finset 6521).card = 6531 := by native_decide
theorem BSD_E143_card_p6529 : (E143_Finset 6529).card = 6544 := by native_decide
theorem BSD_E143_card_p6547 : (E143_Finset 6547).card = 6606 := by native_decide
theorem BSD_E143_card_p6551 : (E143_Finset 6551).card = 6638 := by native_decide
theorem BSD_E143_card_p6553 : (E143_Finset 6553).card = 6574 := by native_decide
theorem BSD_E143_card_p6563 : (E143_Finset 6563).card = 6464 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6469 : a_p 6469 = (31 : ℤ) := by
  have h := BSD_E143_card_p6469; unfold a_p; omega
theorem BSD_ap_p6473 : a_p 6473 = (33 : ℤ) := by
  have h := BSD_E143_card_p6473; unfold a_p; omega
theorem BSD_ap_p6481 : a_p 6481 = (146 : ℤ) := by
  have h := BSD_E143_card_p6481; unfold a_p; omega
theorem BSD_ap_p6491 : a_p 6491 = (-75 : ℤ) := by
  have h := BSD_E143_card_p6491; unfold a_p; omega
theorem BSD_ap_p6521 : a_p 6521 = (-9 : ℤ) := by
  have h := BSD_E143_card_p6521; unfold a_p; omega
theorem BSD_ap_p6529 : a_p 6529 = (-14 : ℤ) := by
  have h := BSD_E143_card_p6529; unfold a_p; omega
theorem BSD_ap_p6547 : a_p 6547 = (-58 : ℤ) := by
  have h := BSD_E143_card_p6547; unfold a_p; omega
theorem BSD_ap_p6551 : a_p 6551 = (-86 : ℤ) := by
  have h := BSD_E143_card_p6551; unfold a_p; omega
theorem BSD_ap_p6553 : a_p 6553 = (-20 : ℤ) := by
  have h := BSD_E143_card_p6553; unfold a_p; omega
theorem BSD_ap_p6563 : a_p 6563 = (100 : ℤ) := by
  have h := BSD_E143_card_p6563; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6469: a_p=+31, 4p-a_p²=24915
theorem BSD_DegreeNonneg_p6469 : BSD_FrobeniusDegreeNonneg_OPEN 6469 := fun r => by
  have hap : (a_p 6469 : ℝ) = 31 := by exact_mod_cast BSD_ap_p6469
  have key : r ^ 2 - (a_p 6469 : ℝ) * r + ((6469 : ℕ) : ℝ) =
      (r - 31/2) ^ 2 + 24915/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (31 : ℝ)/2)]

-- p=6473: a_p=+33, 4p-a_p²=24803
theorem BSD_DegreeNonneg_p6473 : BSD_FrobeniusDegreeNonneg_OPEN 6473 := fun r => by
  have hap : (a_p 6473 : ℝ) = 33 := by exact_mod_cast BSD_ap_p6473
  have key : r ^ 2 - (a_p 6473 : ℝ) * r + ((6473 : ℕ) : ℝ) =
      (r - 33/2) ^ 2 + 24803/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (33 : ℝ)/2)]

-- p=6481: a_p=+146, 4p-a_p²=4608
theorem BSD_DegreeNonneg_p6481 : BSD_FrobeniusDegreeNonneg_OPEN 6481 := fun r => by
  have hap : (a_p 6481 : ℝ) = 146 := by exact_mod_cast BSD_ap_p6481
  have key : r ^ 2 - (a_p 6481 : ℝ) * r + ((6481 : ℕ) : ℝ) =
      (r - 146/2) ^ 2 + 4608/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (146 : ℝ)/2)]

-- p=6491: a_p=-75, 4p-a_p²=20339
theorem BSD_DegreeNonneg_p6491 : BSD_FrobeniusDegreeNonneg_OPEN 6491 := fun r => by
  have hap : (a_p 6491 : ℝ) = -75 := by exact_mod_cast BSD_ap_p6491
  have key : r ^ 2 - (a_p 6491 : ℝ) * r + ((6491 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 20339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

-- p=6521: a_p=-9, 4p-a_p²=26003
theorem BSD_DegreeNonneg_p6521 : BSD_FrobeniusDegreeNonneg_OPEN 6521 := fun r => by
  have hap : (a_p 6521 : ℝ) = -9 := by exact_mod_cast BSD_ap_p6521
  have key : r ^ 2 - (a_p 6521 : ℝ) * r + ((6521 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 26003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

-- p=6529: a_p=-14, 4p-a_p²=25920
theorem BSD_DegreeNonneg_p6529 : BSD_FrobeniusDegreeNonneg_OPEN 6529 := fun r => by
  have hap : (a_p 6529 : ℝ) = -14 := by exact_mod_cast BSD_ap_p6529
  have key : r ^ 2 - (a_p 6529 : ℝ) * r + ((6529 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 25920/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

-- p=6547: a_p=-58, 4p-a_p²=22824
theorem BSD_DegreeNonneg_p6547 : BSD_FrobeniusDegreeNonneg_OPEN 6547 := fun r => by
  have hap : (a_p 6547 : ℝ) = -58 := by exact_mod_cast BSD_ap_p6547
  have key : r ^ 2 - (a_p 6547 : ℝ) * r + ((6547 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 22824/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=6551: a_p=-86, 4p-a_p²=18808
theorem BSD_DegreeNonneg_p6551 : BSD_FrobeniusDegreeNonneg_OPEN 6551 := fun r => by
  have hap : (a_p 6551 : ℝ) = -86 := by exact_mod_cast BSD_ap_p6551
  have key : r ^ 2 - (a_p 6551 : ℝ) * r + ((6551 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 18808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

-- p=6553: a_p=-20, 4p-a_p²=25812
theorem BSD_DegreeNonneg_p6553 : BSD_FrobeniusDegreeNonneg_OPEN 6553 := fun r => by
  have hap : (a_p 6553 : ℝ) = -20 := by exact_mod_cast BSD_ap_p6553
  have key : r ^ 2 - (a_p 6553 : ℝ) * r + ((6553 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 25812/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=6563: a_p=+100, 4p-a_p²=16252
theorem BSD_DegreeNonneg_p6563 : BSD_FrobeniusDegreeNonneg_OPEN 6563 := fun r => by
  have hap : (a_p 6563 : ℝ) = 100 := by exact_mod_cast BSD_ap_p6563
  have key : r ^ 2 - (a_p 6563 : ℝ) * r + ((6563 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 16252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6469 : BSD_Hasse_OPEN 6469 :=
  BSD_hasse_of_degree_nonneg 6469 BSD_DegreeNonneg_p6469
theorem BSD_Hasse_OPEN_p6473 : BSD_Hasse_OPEN 6473 :=
  BSD_hasse_of_degree_nonneg 6473 BSD_DegreeNonneg_p6473
theorem BSD_Hasse_OPEN_p6481 : BSD_Hasse_OPEN 6481 :=
  BSD_hasse_of_degree_nonneg 6481 BSD_DegreeNonneg_p6481
theorem BSD_Hasse_OPEN_p6491 : BSD_Hasse_OPEN 6491 :=
  BSD_hasse_of_degree_nonneg 6491 BSD_DegreeNonneg_p6491
theorem BSD_Hasse_OPEN_p6521 : BSD_Hasse_OPEN 6521 :=
  BSD_hasse_of_degree_nonneg 6521 BSD_DegreeNonneg_p6521
theorem BSD_Hasse_OPEN_p6529 : BSD_Hasse_OPEN 6529 :=
  BSD_hasse_of_degree_nonneg 6529 BSD_DegreeNonneg_p6529
theorem BSD_Hasse_OPEN_p6547 : BSD_Hasse_OPEN 6547 :=
  BSD_hasse_of_degree_nonneg 6547 BSD_DegreeNonneg_p6547
theorem BSD_Hasse_OPEN_p6551 : BSD_Hasse_OPEN 6551 :=
  BSD_hasse_of_degree_nonneg 6551 BSD_DegreeNonneg_p6551
theorem BSD_Hasse_OPEN_p6553 : BSD_Hasse_OPEN 6553 :=
  BSD_hasse_of_degree_nonneg 6553 BSD_DegreeNonneg_p6553
theorem BSD_Hasse_OPEN_p6563 : BSD_Hasse_OPEN 6563 :=
  BSD_hasse_of_degree_nonneg 6563 BSD_DegreeNonneg_p6563

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6469 : (a_p 6469 : ℝ) ^ 2 ≤ 4 * (6469 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6469
theorem BSD_HasseBound_Disc_p6473 : (a_p 6473 : ℝ) ^ 2 ≤ 4 * (6473 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6473
theorem BSD_HasseBound_Disc_p6481 : (a_p 6481 : ℝ) ^ 2 ≤ 4 * (6481 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6481
theorem BSD_HasseBound_Disc_p6491 : (a_p 6491 : ℝ) ^ 2 ≤ 4 * (6491 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6491
theorem BSD_HasseBound_Disc_p6521 : (a_p 6521 : ℝ) ^ 2 ≤ 4 * (6521 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6521
theorem BSD_HasseBound_Disc_p6529 : (a_p 6529 : ℝ) ^ 2 ≤ 4 * (6529 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6529
theorem BSD_HasseBound_Disc_p6547 : (a_p 6547 : ℝ) ^ 2 ≤ 4 * (6547 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6547
theorem BSD_HasseBound_Disc_p6551 : (a_p 6551 : ℝ) ^ 2 ≤ 4 * (6551 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6551
theorem BSD_HasseBound_Disc_p6553 : (a_p 6553 : ℝ) ^ 2 ≤ 4 * (6553 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6553
theorem BSD_HasseBound_Disc_p6563 : (a_p 6563 : ℝ) ^ 2 ≤ 4 * (6563 : ℝ) :=
  BSD_disc_from_deg_850 BSD_DegreeNonneg_p6563

end Towers.BSD