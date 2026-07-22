/-
================================================================
Towers / BSD / BSD_Genesis886_CLOSED  (genesis-886)

HasseBridge Tier C: Hasse bounds for primes
9721..9791 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9721: card=9622, a_p=+100, disc=-28884
  p=9733: card=9753, a_p=-19, disc=-38571
  p=9739: card=9841, a_p=-101, disc=-28755
  p=9743: card=9788, a_p=-44, disc=-37036
  p=9749: card=9664, a_p=+86, disc=-31600
  p=9767: card=9750, a_p=+18, disc=-38744
  p=9769: card=9709, a_p=+61, disc=-35355
  p=9781: card=9694, a_p=+88, disc=-31380
  p=9787: card=9910, a_p=-122, disc=-24264
  p=9791: card=9904, a_p=-112, disc=-26620

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_886 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i886_p9721 : Fact (9721 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9733 : Fact (9733 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9739 : Fact (9739 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9743 : Fact (9743 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9749 : Fact (9749 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9767 : Fact (9767 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9769 : Fact (9769 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9781 : Fact (9781 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9787 : Fact (9787 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9791 : Fact (9791 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9721 : (E143_Finset 9721).card = 9622 := by native_decide
theorem BSD_E143_card_p9733 : (E143_Finset 9733).card = 9753 := by native_decide
theorem BSD_E143_card_p9739 : (E143_Finset 9739).card = 9841 := by native_decide
theorem BSD_E143_card_p9743 : (E143_Finset 9743).card = 9788 := by native_decide
theorem BSD_E143_card_p9749 : (E143_Finset 9749).card = 9664 := by native_decide
theorem BSD_E143_card_p9767 : (E143_Finset 9767).card = 9750 := by native_decide
theorem BSD_E143_card_p9769 : (E143_Finset 9769).card = 9709 := by native_decide
theorem BSD_E143_card_p9781 : (E143_Finset 9781).card = 9694 := by native_decide
theorem BSD_E143_card_p9787 : (E143_Finset 9787).card = 9910 := by native_decide
theorem BSD_E143_card_p9791 : (E143_Finset 9791).card = 9904 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9721 : a_p 9721 = (100 : ℤ) := by
  have h := BSD_E143_card_p9721; unfold a_p; omega
theorem BSD_ap_p9733 : a_p 9733 = (-19 : ℤ) := by
  have h := BSD_E143_card_p9733; unfold a_p; omega
theorem BSD_ap_p9739 : a_p 9739 = (-101 : ℤ) := by
  have h := BSD_E143_card_p9739; unfold a_p; omega
theorem BSD_ap_p9743 : a_p 9743 = (-44 : ℤ) := by
  have h := BSD_E143_card_p9743; unfold a_p; omega
theorem BSD_ap_p9749 : a_p 9749 = (86 : ℤ) := by
  have h := BSD_E143_card_p9749; unfold a_p; omega
theorem BSD_ap_p9767 : a_p 9767 = (18 : ℤ) := by
  have h := BSD_E143_card_p9767; unfold a_p; omega
theorem BSD_ap_p9769 : a_p 9769 = (61 : ℤ) := by
  have h := BSD_E143_card_p9769; unfold a_p; omega
theorem BSD_ap_p9781 : a_p 9781 = (88 : ℤ) := by
  have h := BSD_E143_card_p9781; unfold a_p; omega
theorem BSD_ap_p9787 : a_p 9787 = (-122 : ℤ) := by
  have h := BSD_E143_card_p9787; unfold a_p; omega
theorem BSD_ap_p9791 : a_p 9791 = (-112 : ℤ) := by
  have h := BSD_E143_card_p9791; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9721: a_p=+100, 4p-a_p²=28884
theorem BSD_DegreeNonneg_p9721 : BSD_FrobeniusDegreeNonneg_OPEN 9721 := fun r => by
  have hap : (a_p 9721 : ℝ) = 100 := by exact_mod_cast BSD_ap_p9721
  have key : r ^ 2 - (a_p 9721 : ℝ) * r + ((9721 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 28884/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

-- p=9733: a_p=-19, 4p-a_p²=38571
theorem BSD_DegreeNonneg_p9733 : BSD_FrobeniusDegreeNonneg_OPEN 9733 := fun r => by
  have hap : (a_p 9733 : ℝ) = -19 := by exact_mod_cast BSD_ap_p9733
  have key : r ^ 2 - (a_p 9733 : ℝ) * r + ((9733 : ℕ) : ℝ) =
      (r + 19/2) ^ 2 + 38571/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (19 : ℝ)/2)]

-- p=9739: a_p=-101, 4p-a_p²=28755
theorem BSD_DegreeNonneg_p9739 : BSD_FrobeniusDegreeNonneg_OPEN 9739 := fun r => by
  have hap : (a_p 9739 : ℝ) = -101 := by exact_mod_cast BSD_ap_p9739
  have key : r ^ 2 - (a_p 9739 : ℝ) * r + ((9739 : ℕ) : ℝ) =
      (r + 101/2) ^ 2 + 28755/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (101 : ℝ)/2)]

-- p=9743: a_p=-44, 4p-a_p²=37036
theorem BSD_DegreeNonneg_p9743 : BSD_FrobeniusDegreeNonneg_OPEN 9743 := fun r => by
  have hap : (a_p 9743 : ℝ) = -44 := by exact_mod_cast BSD_ap_p9743
  have key : r ^ 2 - (a_p 9743 : ℝ) * r + ((9743 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 37036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

-- p=9749: a_p=+86, 4p-a_p²=31600
theorem BSD_DegreeNonneg_p9749 : BSD_FrobeniusDegreeNonneg_OPEN 9749 := fun r => by
  have hap : (a_p 9749 : ℝ) = 86 := by exact_mod_cast BSD_ap_p9749
  have key : r ^ 2 - (a_p 9749 : ℝ) * r + ((9749 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 31600/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

-- p=9767: a_p=+18, 4p-a_p²=38744
theorem BSD_DegreeNonneg_p9767 : BSD_FrobeniusDegreeNonneg_OPEN 9767 := fun r => by
  have hap : (a_p 9767 : ℝ) = 18 := by exact_mod_cast BSD_ap_p9767
  have key : r ^ 2 - (a_p 9767 : ℝ) * r + ((9767 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 38744/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=9769: a_p=+61, 4p-a_p²=35355
theorem BSD_DegreeNonneg_p9769 : BSD_FrobeniusDegreeNonneg_OPEN 9769 := fun r => by
  have hap : (a_p 9769 : ℝ) = 61 := by exact_mod_cast BSD_ap_p9769
  have key : r ^ 2 - (a_p 9769 : ℝ) * r + ((9769 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 35355/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

-- p=9781: a_p=+88, 4p-a_p²=31380
theorem BSD_DegreeNonneg_p9781 : BSD_FrobeniusDegreeNonneg_OPEN 9781 := fun r => by
  have hap : (a_p 9781 : ℝ) = 88 := by exact_mod_cast BSD_ap_p9781
  have key : r ^ 2 - (a_p 9781 : ℝ) * r + ((9781 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 31380/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

-- p=9787: a_p=-122, 4p-a_p²=24264
theorem BSD_DegreeNonneg_p9787 : BSD_FrobeniusDegreeNonneg_OPEN 9787 := fun r => by
  have hap : (a_p 9787 : ℝ) = -122 := by exact_mod_cast BSD_ap_p9787
  have key : r ^ 2 - (a_p 9787 : ℝ) * r + ((9787 : ℕ) : ℝ) =
      (r + 122/2) ^ 2 + 24264/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (122 : ℝ)/2)]

-- p=9791: a_p=-112, 4p-a_p²=26620
theorem BSD_DegreeNonneg_p9791 : BSD_FrobeniusDegreeNonneg_OPEN 9791 := fun r => by
  have hap : (a_p 9791 : ℝ) = -112 := by exact_mod_cast BSD_ap_p9791
  have key : r ^ 2 - (a_p 9791 : ℝ) * r + ((9791 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 26620/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9721 : BSD_Hasse_OPEN 9721 :=
  BSD_hasse_of_degree_nonneg 9721 BSD_DegreeNonneg_p9721
theorem BSD_Hasse_OPEN_p9733 : BSD_Hasse_OPEN 9733 :=
  BSD_hasse_of_degree_nonneg 9733 BSD_DegreeNonneg_p9733
theorem BSD_Hasse_OPEN_p9739 : BSD_Hasse_OPEN 9739 :=
  BSD_hasse_of_degree_nonneg 9739 BSD_DegreeNonneg_p9739
theorem BSD_Hasse_OPEN_p9743 : BSD_Hasse_OPEN 9743 :=
  BSD_hasse_of_degree_nonneg 9743 BSD_DegreeNonneg_p9743
theorem BSD_Hasse_OPEN_p9749 : BSD_Hasse_OPEN 9749 :=
  BSD_hasse_of_degree_nonneg 9749 BSD_DegreeNonneg_p9749
theorem BSD_Hasse_OPEN_p9767 : BSD_Hasse_OPEN 9767 :=
  BSD_hasse_of_degree_nonneg 9767 BSD_DegreeNonneg_p9767
theorem BSD_Hasse_OPEN_p9769 : BSD_Hasse_OPEN 9769 :=
  BSD_hasse_of_degree_nonneg 9769 BSD_DegreeNonneg_p9769
theorem BSD_Hasse_OPEN_p9781 : BSD_Hasse_OPEN 9781 :=
  BSD_hasse_of_degree_nonneg 9781 BSD_DegreeNonneg_p9781
theorem BSD_Hasse_OPEN_p9787 : BSD_Hasse_OPEN 9787 :=
  BSD_hasse_of_degree_nonneg 9787 BSD_DegreeNonneg_p9787
theorem BSD_Hasse_OPEN_p9791 : BSD_Hasse_OPEN 9791 :=
  BSD_hasse_of_degree_nonneg 9791 BSD_DegreeNonneg_p9791

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9721 : (a_p 9721 : ℝ) ^ 2 ≤ 4 * (9721 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9721
theorem BSD_HasseBound_Disc_p9733 : (a_p 9733 : ℝ) ^ 2 ≤ 4 * (9733 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9733
theorem BSD_HasseBound_Disc_p9739 : (a_p 9739 : ℝ) ^ 2 ≤ 4 * (9739 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9739
theorem BSD_HasseBound_Disc_p9743 : (a_p 9743 : ℝ) ^ 2 ≤ 4 * (9743 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9743
theorem BSD_HasseBound_Disc_p9749 : (a_p 9749 : ℝ) ^ 2 ≤ 4 * (9749 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9749
theorem BSD_HasseBound_Disc_p9767 : (a_p 9767 : ℝ) ^ 2 ≤ 4 * (9767 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9767
theorem BSD_HasseBound_Disc_p9769 : (a_p 9769 : ℝ) ^ 2 ≤ 4 * (9769 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9769
theorem BSD_HasseBound_Disc_p9781 : (a_p 9781 : ℝ) ^ 2 ≤ 4 * (9781 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9781
theorem BSD_HasseBound_Disc_p9787 : (a_p 9787 : ℝ) ^ 2 ≤ 4 * (9787 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9787
theorem BSD_HasseBound_Disc_p9791 : (a_p 9791 : ℝ) ^ 2 ≤ 4 * (9791 : ℝ) :=
  BSD_disc_from_deg_886 BSD_DegreeNonneg_p9791

end Towers.BSD