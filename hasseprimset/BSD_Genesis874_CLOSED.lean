/-
================================================================
Towers / BSD / BSD_Genesis874_CLOSED  (genesis-874)

HasseBridge Tier C: Hasse bounds for primes
8669..8731 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8669: card=8708, a_p=-38, disc=-33232
  p=8677: card=8736, a_p=-58, disc=-31344
  p=8681: card=8640, a_p=+42, disc=-32960
  p=8689: card=8644, a_p=+46, disc=-32640
  p=8693: card=8588, a_p=+106, disc=-23536
  p=8699: card=8547, a_p=+153, disc=-11387
  p=8707: card=8686, a_p=+22, disc=-34344
  p=8713: card=8623, a_p=+91, disc=-26571
  p=8719: card=8550, a_p=+170, disc=-5976
  p=8731: card=8680, a_p=+52, disc=-32220

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_874 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i874_p8669 : Fact (8669 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8677 : Fact (8677 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8681 : Fact (8681 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8689 : Fact (8689 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8693 : Fact (8693 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8699 : Fact (8699 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8707 : Fact (8707 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8713 : Fact (8713 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8719 : Fact (8719 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8731 : Fact (8731 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8669 : (E143_Finset 8669).card = 8708 := by native_decide
theorem BSD_E143_card_p8677 : (E143_Finset 8677).card = 8736 := by native_decide
theorem BSD_E143_card_p8681 : (E143_Finset 8681).card = 8640 := by native_decide
theorem BSD_E143_card_p8689 : (E143_Finset 8689).card = 8644 := by native_decide
theorem BSD_E143_card_p8693 : (E143_Finset 8693).card = 8588 := by native_decide
theorem BSD_E143_card_p8699 : (E143_Finset 8699).card = 8547 := by native_decide
theorem BSD_E143_card_p8707 : (E143_Finset 8707).card = 8686 := by native_decide
theorem BSD_E143_card_p8713 : (E143_Finset 8713).card = 8623 := by native_decide
theorem BSD_E143_card_p8719 : (E143_Finset 8719).card = 8550 := by native_decide
theorem BSD_E143_card_p8731 : (E143_Finset 8731).card = 8680 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8669 : a_p 8669 = (-38 : ℤ) := by
  have h := BSD_E143_card_p8669; unfold a_p; omega
theorem BSD_ap_p8677 : a_p 8677 = (-58 : ℤ) := by
  have h := BSD_E143_card_p8677; unfold a_p; omega
theorem BSD_ap_p8681 : a_p 8681 = (42 : ℤ) := by
  have h := BSD_E143_card_p8681; unfold a_p; omega
theorem BSD_ap_p8689 : a_p 8689 = (46 : ℤ) := by
  have h := BSD_E143_card_p8689; unfold a_p; omega
theorem BSD_ap_p8693 : a_p 8693 = (106 : ℤ) := by
  have h := BSD_E143_card_p8693; unfold a_p; omega
theorem BSD_ap_p8699 : a_p 8699 = (153 : ℤ) := by
  have h := BSD_E143_card_p8699; unfold a_p; omega
theorem BSD_ap_p8707 : a_p 8707 = (22 : ℤ) := by
  have h := BSD_E143_card_p8707; unfold a_p; omega
theorem BSD_ap_p8713 : a_p 8713 = (91 : ℤ) := by
  have h := BSD_E143_card_p8713; unfold a_p; omega
theorem BSD_ap_p8719 : a_p 8719 = (170 : ℤ) := by
  have h := BSD_E143_card_p8719; unfold a_p; omega
theorem BSD_ap_p8731 : a_p 8731 = (52 : ℤ) := by
  have h := BSD_E143_card_p8731; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8669: a_p=-38, 4p-a_p²=33232
theorem BSD_DegreeNonneg_p8669 : BSD_FrobeniusDegreeNonneg_OPEN 8669 := fun r => by
  have hap : (a_p 8669 : ℝ) = -38 := by exact_mod_cast BSD_ap_p8669
  have key : r ^ 2 - (a_p 8669 : ℝ) * r + ((8669 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 33232/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

-- p=8677: a_p=-58, 4p-a_p²=31344
theorem BSD_DegreeNonneg_p8677 : BSD_FrobeniusDegreeNonneg_OPEN 8677 := fun r => by
  have hap : (a_p 8677 : ℝ) = -58 := by exact_mod_cast BSD_ap_p8677
  have key : r ^ 2 - (a_p 8677 : ℝ) * r + ((8677 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 31344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=8681: a_p=+42, 4p-a_p²=32960
theorem BSD_DegreeNonneg_p8681 : BSD_FrobeniusDegreeNonneg_OPEN 8681 := fun r => by
  have hap : (a_p 8681 : ℝ) = 42 := by exact_mod_cast BSD_ap_p8681
  have key : r ^ 2 - (a_p 8681 : ℝ) * r + ((8681 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 32960/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

-- p=8689: a_p=+46, 4p-a_p²=32640
theorem BSD_DegreeNonneg_p8689 : BSD_FrobeniusDegreeNonneg_OPEN 8689 := fun r => by
  have hap : (a_p 8689 : ℝ) = 46 := by exact_mod_cast BSD_ap_p8689
  have key : r ^ 2 - (a_p 8689 : ℝ) * r + ((8689 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 32640/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=8693: a_p=+106, 4p-a_p²=23536
theorem BSD_DegreeNonneg_p8693 : BSD_FrobeniusDegreeNonneg_OPEN 8693 := fun r => by
  have hap : (a_p 8693 : ℝ) = 106 := by exact_mod_cast BSD_ap_p8693
  have key : r ^ 2 - (a_p 8693 : ℝ) * r + ((8693 : ℕ) : ℝ) =
      (r - 106/2) ^ 2 + 23536/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (106 : ℝ)/2)]

-- p=8699: a_p=+153, 4p-a_p²=11387
theorem BSD_DegreeNonneg_p8699 : BSD_FrobeniusDegreeNonneg_OPEN 8699 := fun r => by
  have hap : (a_p 8699 : ℝ) = 153 := by exact_mod_cast BSD_ap_p8699
  have key : r ^ 2 - (a_p 8699 : ℝ) * r + ((8699 : ℕ) : ℝ) =
      (r - 153/2) ^ 2 + 11387/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (153 : ℝ)/2)]

-- p=8707: a_p=+22, 4p-a_p²=34344
theorem BSD_DegreeNonneg_p8707 : BSD_FrobeniusDegreeNonneg_OPEN 8707 := fun r => by
  have hap : (a_p 8707 : ℝ) = 22 := by exact_mod_cast BSD_ap_p8707
  have key : r ^ 2 - (a_p 8707 : ℝ) * r + ((8707 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 34344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

-- p=8713: a_p=+91, 4p-a_p²=26571
theorem BSD_DegreeNonneg_p8713 : BSD_FrobeniusDegreeNonneg_OPEN 8713 := fun r => by
  have hap : (a_p 8713 : ℝ) = 91 := by exact_mod_cast BSD_ap_p8713
  have key : r ^ 2 - (a_p 8713 : ℝ) * r + ((8713 : ℕ) : ℝ) =
      (r - 91/2) ^ 2 + 26571/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (91 : ℝ)/2)]

-- p=8719: a_p=+170, 4p-a_p²=5976
theorem BSD_DegreeNonneg_p8719 : BSD_FrobeniusDegreeNonneg_OPEN 8719 := fun r => by
  have hap : (a_p 8719 : ℝ) = 170 := by exact_mod_cast BSD_ap_p8719
  have key : r ^ 2 - (a_p 8719 : ℝ) * r + ((8719 : ℕ) : ℝ) =
      (r - 170/2) ^ 2 + 5976/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (170 : ℝ)/2)]

-- p=8731: a_p=+52, 4p-a_p²=32220
theorem BSD_DegreeNonneg_p8731 : BSD_FrobeniusDegreeNonneg_OPEN 8731 := fun r => by
  have hap : (a_p 8731 : ℝ) = 52 := by exact_mod_cast BSD_ap_p8731
  have key : r ^ 2 - (a_p 8731 : ℝ) * r + ((8731 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 32220/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8669 : BSD_Hasse_OPEN 8669 :=
  BSD_hasse_of_degree_nonneg 8669 BSD_DegreeNonneg_p8669
theorem BSD_Hasse_OPEN_p8677 : BSD_Hasse_OPEN 8677 :=
  BSD_hasse_of_degree_nonneg 8677 BSD_DegreeNonneg_p8677
theorem BSD_Hasse_OPEN_p8681 : BSD_Hasse_OPEN 8681 :=
  BSD_hasse_of_degree_nonneg 8681 BSD_DegreeNonneg_p8681
theorem BSD_Hasse_OPEN_p8689 : BSD_Hasse_OPEN 8689 :=
  BSD_hasse_of_degree_nonneg 8689 BSD_DegreeNonneg_p8689
theorem BSD_Hasse_OPEN_p8693 : BSD_Hasse_OPEN 8693 :=
  BSD_hasse_of_degree_nonneg 8693 BSD_DegreeNonneg_p8693
theorem BSD_Hasse_OPEN_p8699 : BSD_Hasse_OPEN 8699 :=
  BSD_hasse_of_degree_nonneg 8699 BSD_DegreeNonneg_p8699
theorem BSD_Hasse_OPEN_p8707 : BSD_Hasse_OPEN 8707 :=
  BSD_hasse_of_degree_nonneg 8707 BSD_DegreeNonneg_p8707
theorem BSD_Hasse_OPEN_p8713 : BSD_Hasse_OPEN 8713 :=
  BSD_hasse_of_degree_nonneg 8713 BSD_DegreeNonneg_p8713
theorem BSD_Hasse_OPEN_p8719 : BSD_Hasse_OPEN 8719 :=
  BSD_hasse_of_degree_nonneg 8719 BSD_DegreeNonneg_p8719
theorem BSD_Hasse_OPEN_p8731 : BSD_Hasse_OPEN 8731 :=
  BSD_hasse_of_degree_nonneg 8731 BSD_DegreeNonneg_p8731

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8669 : (a_p 8669 : ℝ) ^ 2 ≤ 4 * (8669 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8669
theorem BSD_HasseBound_Disc_p8677 : (a_p 8677 : ℝ) ^ 2 ≤ 4 * (8677 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8677
theorem BSD_HasseBound_Disc_p8681 : (a_p 8681 : ℝ) ^ 2 ≤ 4 * (8681 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8681
theorem BSD_HasseBound_Disc_p8689 : (a_p 8689 : ℝ) ^ 2 ≤ 4 * (8689 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8689
theorem BSD_HasseBound_Disc_p8693 : (a_p 8693 : ℝ) ^ 2 ≤ 4 * (8693 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8693
theorem BSD_HasseBound_Disc_p8699 : (a_p 8699 : ℝ) ^ 2 ≤ 4 * (8699 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8699
theorem BSD_HasseBound_Disc_p8707 : (a_p 8707 : ℝ) ^ 2 ≤ 4 * (8707 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8707
theorem BSD_HasseBound_Disc_p8713 : (a_p 8713 : ℝ) ^ 2 ≤ 4 * (8713 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8713
theorem BSD_HasseBound_Disc_p8719 : (a_p 8719 : ℝ) ^ 2 ≤ 4 * (8719 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8719
theorem BSD_HasseBound_Disc_p8731 : (a_p 8731 : ℝ) ^ 2 ≤ 4 * (8731 : ℝ) :=
  BSD_disc_from_deg_874 BSD_DegreeNonneg_p8731

end Towers.BSD