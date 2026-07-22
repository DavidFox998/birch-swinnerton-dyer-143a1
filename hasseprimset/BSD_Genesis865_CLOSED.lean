/-
================================================================
Towers / BSD / BSD_Genesis865_CLOSED  (genesis-865)

HasseBridge Tier C: Hasse bounds for primes
7823..7901 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7823: card=7716, a_p=+108, disc=-19628
  p=7829: card=7758, a_p=+72, disc=-26132
  p=7841: card=7911, a_p=-69, disc=-26603
  p=7853: card=7860, a_p=-6, disc=-31376
  p=7867: card=7936, a_p=-68, disc=-26844
  p=7873: card=7986, a_p=-112, disc=-18948
  p=7877: card=7764, a_p=+114, disc=-18512
  p=7879: card=7801, a_p=+79, disc=-25275
  p=7883: card=7862, a_p=+22, disc=-31048
  p=7901: card=7903, a_p=-1, disc=-31603

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_865 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i865_p7823 : Fact (7823 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7829 : Fact (7829 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7841 : Fact (7841 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7853 : Fact (7853 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7867 : Fact (7867 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7873 : Fact (7873 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7877 : Fact (7877 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7879 : Fact (7879 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7883 : Fact (7883 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7901 : Fact (7901 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7823 : (E143_Finset 7823).card = 7716 := by native_decide
theorem BSD_E143_card_p7829 : (E143_Finset 7829).card = 7758 := by native_decide
theorem BSD_E143_card_p7841 : (E143_Finset 7841).card = 7911 := by native_decide
theorem BSD_E143_card_p7853 : (E143_Finset 7853).card = 7860 := by native_decide
theorem BSD_E143_card_p7867 : (E143_Finset 7867).card = 7936 := by native_decide
theorem BSD_E143_card_p7873 : (E143_Finset 7873).card = 7986 := by native_decide
theorem BSD_E143_card_p7877 : (E143_Finset 7877).card = 7764 := by native_decide
theorem BSD_E143_card_p7879 : (E143_Finset 7879).card = 7801 := by native_decide
theorem BSD_E143_card_p7883 : (E143_Finset 7883).card = 7862 := by native_decide
theorem BSD_E143_card_p7901 : (E143_Finset 7901).card = 7903 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7823 : a_p 7823 = (108 : ℤ) := by
  have h := BSD_E143_card_p7823; unfold a_p; omega
theorem BSD_ap_p7829 : a_p 7829 = (72 : ℤ) := by
  have h := BSD_E143_card_p7829; unfold a_p; omega
theorem BSD_ap_p7841 : a_p 7841 = (-69 : ℤ) := by
  have h := BSD_E143_card_p7841; unfold a_p; omega
theorem BSD_ap_p7853 : a_p 7853 = (-6 : ℤ) := by
  have h := BSD_E143_card_p7853; unfold a_p; omega
theorem BSD_ap_p7867 : a_p 7867 = (-68 : ℤ) := by
  have h := BSD_E143_card_p7867; unfold a_p; omega
theorem BSD_ap_p7873 : a_p 7873 = (-112 : ℤ) := by
  have h := BSD_E143_card_p7873; unfold a_p; omega
theorem BSD_ap_p7877 : a_p 7877 = (114 : ℤ) := by
  have h := BSD_E143_card_p7877; unfold a_p; omega
theorem BSD_ap_p7879 : a_p 7879 = (79 : ℤ) := by
  have h := BSD_E143_card_p7879; unfold a_p; omega
theorem BSD_ap_p7883 : a_p 7883 = (22 : ℤ) := by
  have h := BSD_E143_card_p7883; unfold a_p; omega
theorem BSD_ap_p7901 : a_p 7901 = (-1 : ℤ) := by
  have h := BSD_E143_card_p7901; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7823: a_p=+108, 4p-a_p²=19628
theorem BSD_DegreeNonneg_p7823 : BSD_FrobeniusDegreeNonneg_OPEN 7823 := fun r => by
  have hap : (a_p 7823 : ℝ) = 108 := by exact_mod_cast BSD_ap_p7823
  have key : r ^ 2 - (a_p 7823 : ℝ) * r + ((7823 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 19628/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

-- p=7829: a_p=+72, 4p-a_p²=26132
theorem BSD_DegreeNonneg_p7829 : BSD_FrobeniusDegreeNonneg_OPEN 7829 := fun r => by
  have hap : (a_p 7829 : ℝ) = 72 := by exact_mod_cast BSD_ap_p7829
  have key : r ^ 2 - (a_p 7829 : ℝ) * r + ((7829 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 26132/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

-- p=7841: a_p=-69, 4p-a_p²=26603
theorem BSD_DegreeNonneg_p7841 : BSD_FrobeniusDegreeNonneg_OPEN 7841 := fun r => by
  have hap : (a_p 7841 : ℝ) = -69 := by exact_mod_cast BSD_ap_p7841
  have key : r ^ 2 - (a_p 7841 : ℝ) * r + ((7841 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 26603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

-- p=7853: a_p=-6, 4p-a_p²=31376
theorem BSD_DegreeNonneg_p7853 : BSD_FrobeniusDegreeNonneg_OPEN 7853 := fun r => by
  have hap : (a_p 7853 : ℝ) = -6 := by exact_mod_cast BSD_ap_p7853
  have key : r ^ 2 - (a_p 7853 : ℝ) * r + ((7853 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 31376/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

-- p=7867: a_p=-68, 4p-a_p²=26844
theorem BSD_DegreeNonneg_p7867 : BSD_FrobeniusDegreeNonneg_OPEN 7867 := fun r => by
  have hap : (a_p 7867 : ℝ) = -68 := by exact_mod_cast BSD_ap_p7867
  have key : r ^ 2 - (a_p 7867 : ℝ) * r + ((7867 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 26844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

-- p=7873: a_p=-112, 4p-a_p²=18948
theorem BSD_DegreeNonneg_p7873 : BSD_FrobeniusDegreeNonneg_OPEN 7873 := fun r => by
  have hap : (a_p 7873 : ℝ) = -112 := by exact_mod_cast BSD_ap_p7873
  have key : r ^ 2 - (a_p 7873 : ℝ) * r + ((7873 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 18948/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

-- p=7877: a_p=+114, 4p-a_p²=18512
theorem BSD_DegreeNonneg_p7877 : BSD_FrobeniusDegreeNonneg_OPEN 7877 := fun r => by
  have hap : (a_p 7877 : ℝ) = 114 := by exact_mod_cast BSD_ap_p7877
  have key : r ^ 2 - (a_p 7877 : ℝ) * r + ((7877 : ℕ) : ℝ) =
      (r - 114/2) ^ 2 + 18512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (114 : ℝ)/2)]

-- p=7879: a_p=+79, 4p-a_p²=25275
theorem BSD_DegreeNonneg_p7879 : BSD_FrobeniusDegreeNonneg_OPEN 7879 := fun r => by
  have hap : (a_p 7879 : ℝ) = 79 := by exact_mod_cast BSD_ap_p7879
  have key : r ^ 2 - (a_p 7879 : ℝ) * r + ((7879 : ℕ) : ℝ) =
      (r - 79/2) ^ 2 + 25275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (79 : ℝ)/2)]

-- p=7883: a_p=+22, 4p-a_p²=31048
theorem BSD_DegreeNonneg_p7883 : BSD_FrobeniusDegreeNonneg_OPEN 7883 := fun r => by
  have hap : (a_p 7883 : ℝ) = 22 := by exact_mod_cast BSD_ap_p7883
  have key : r ^ 2 - (a_p 7883 : ℝ) * r + ((7883 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 31048/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

-- p=7901: a_p=-1, 4p-a_p²=31603
theorem BSD_DegreeNonneg_p7901 : BSD_FrobeniusDegreeNonneg_OPEN 7901 := fun r => by
  have hap : (a_p 7901 : ℝ) = -1 := by exact_mod_cast BSD_ap_p7901
  have key : r ^ 2 - (a_p 7901 : ℝ) * r + ((7901 : ℕ) : ℝ) =
      (r + 1/2) ^ 2 + 31603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (1 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7823 : BSD_Hasse_OPEN 7823 :=
  BSD_hasse_of_degree_nonneg 7823 BSD_DegreeNonneg_p7823
theorem BSD_Hasse_OPEN_p7829 : BSD_Hasse_OPEN 7829 :=
  BSD_hasse_of_degree_nonneg 7829 BSD_DegreeNonneg_p7829
theorem BSD_Hasse_OPEN_p7841 : BSD_Hasse_OPEN 7841 :=
  BSD_hasse_of_degree_nonneg 7841 BSD_DegreeNonneg_p7841
theorem BSD_Hasse_OPEN_p7853 : BSD_Hasse_OPEN 7853 :=
  BSD_hasse_of_degree_nonneg 7853 BSD_DegreeNonneg_p7853
theorem BSD_Hasse_OPEN_p7867 : BSD_Hasse_OPEN 7867 :=
  BSD_hasse_of_degree_nonneg 7867 BSD_DegreeNonneg_p7867
theorem BSD_Hasse_OPEN_p7873 : BSD_Hasse_OPEN 7873 :=
  BSD_hasse_of_degree_nonneg 7873 BSD_DegreeNonneg_p7873
theorem BSD_Hasse_OPEN_p7877 : BSD_Hasse_OPEN 7877 :=
  BSD_hasse_of_degree_nonneg 7877 BSD_DegreeNonneg_p7877
theorem BSD_Hasse_OPEN_p7879 : BSD_Hasse_OPEN 7879 :=
  BSD_hasse_of_degree_nonneg 7879 BSD_DegreeNonneg_p7879
theorem BSD_Hasse_OPEN_p7883 : BSD_Hasse_OPEN 7883 :=
  BSD_hasse_of_degree_nonneg 7883 BSD_DegreeNonneg_p7883
theorem BSD_Hasse_OPEN_p7901 : BSD_Hasse_OPEN 7901 :=
  BSD_hasse_of_degree_nonneg 7901 BSD_DegreeNonneg_p7901

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7823 : (a_p 7823 : ℝ) ^ 2 ≤ 4 * (7823 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7823
theorem BSD_HasseBound_Disc_p7829 : (a_p 7829 : ℝ) ^ 2 ≤ 4 * (7829 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7829
theorem BSD_HasseBound_Disc_p7841 : (a_p 7841 : ℝ) ^ 2 ≤ 4 * (7841 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7841
theorem BSD_HasseBound_Disc_p7853 : (a_p 7853 : ℝ) ^ 2 ≤ 4 * (7853 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7853
theorem BSD_HasseBound_Disc_p7867 : (a_p 7867 : ℝ) ^ 2 ≤ 4 * (7867 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7867
theorem BSD_HasseBound_Disc_p7873 : (a_p 7873 : ℝ) ^ 2 ≤ 4 * (7873 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7873
theorem BSD_HasseBound_Disc_p7877 : (a_p 7877 : ℝ) ^ 2 ≤ 4 * (7877 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7877
theorem BSD_HasseBound_Disc_p7879 : (a_p 7879 : ℝ) ^ 2 ≤ 4 * (7879 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7879
theorem BSD_HasseBound_Disc_p7883 : (a_p 7883 : ℝ) ^ 2 ≤ 4 * (7883 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7883
theorem BSD_HasseBound_Disc_p7901 : (a_p 7901 : ℝ) ^ 2 ≤ 4 * (7901 : ℝ) :=
  BSD_disc_from_deg_865 BSD_DegreeNonneg_p7901

end Towers.BSD