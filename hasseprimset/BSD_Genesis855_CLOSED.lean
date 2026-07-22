/-
================================================================
Towers / BSD / BSD_Genesis855_CLOSED  (genesis-855)

HasseBridge Tier C: Hasse bounds for primes
6911..6983 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6911: card=6920, a_p=-8, disc=-27580
  p=6917: card=6880, a_p=+38, disc=-26224
  p=6947: card=6882, a_p=+66, disc=-23432
  p=6949: card=7038, a_p=-88, disc=-20052
  p=6959: card=7032, a_p=-72, disc=-22652
  p=6961: card=7028, a_p=-66, disc=-23488
  p=6967: card=6952, a_p=+16, disc=-27612
  p=6971: card=6890, a_p=+82, disc=-21160
  p=6977: card=6843, a_p=+135, disc=-9683
  p=6983: card=7095, a_p=-111, disc=-15611

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_855 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i855_p6911 : Fact (6911 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6917 : Fact (6917 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6947 : Fact (6947 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6949 : Fact (6949 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6959 : Fact (6959 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6961 : Fact (6961 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6967 : Fact (6967 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6971 : Fact (6971 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6977 : Fact (6977 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6983 : Fact (6983 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6911 : (E143_Finset 6911).card = 6920 := by native_decide
theorem BSD_E143_card_p6917 : (E143_Finset 6917).card = 6880 := by native_decide
theorem BSD_E143_card_p6947 : (E143_Finset 6947).card = 6882 := by native_decide
theorem BSD_E143_card_p6949 : (E143_Finset 6949).card = 7038 := by native_decide
theorem BSD_E143_card_p6959 : (E143_Finset 6959).card = 7032 := by native_decide
theorem BSD_E143_card_p6961 : (E143_Finset 6961).card = 7028 := by native_decide
theorem BSD_E143_card_p6967 : (E143_Finset 6967).card = 6952 := by native_decide
theorem BSD_E143_card_p6971 : (E143_Finset 6971).card = 6890 := by native_decide
theorem BSD_E143_card_p6977 : (E143_Finset 6977).card = 6843 := by native_decide
theorem BSD_E143_card_p6983 : (E143_Finset 6983).card = 7095 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6911 : a_p 6911 = (-8 : ℤ) := by
  have h := BSD_E143_card_p6911; unfold a_p; omega
theorem BSD_ap_p6917 : a_p 6917 = (38 : ℤ) := by
  have h := BSD_E143_card_p6917; unfold a_p; omega
theorem BSD_ap_p6947 : a_p 6947 = (66 : ℤ) := by
  have h := BSD_E143_card_p6947; unfold a_p; omega
theorem BSD_ap_p6949 : a_p 6949 = (-88 : ℤ) := by
  have h := BSD_E143_card_p6949; unfold a_p; omega
theorem BSD_ap_p6959 : a_p 6959 = (-72 : ℤ) := by
  have h := BSD_E143_card_p6959; unfold a_p; omega
theorem BSD_ap_p6961 : a_p 6961 = (-66 : ℤ) := by
  have h := BSD_E143_card_p6961; unfold a_p; omega
theorem BSD_ap_p6967 : a_p 6967 = (16 : ℤ) := by
  have h := BSD_E143_card_p6967; unfold a_p; omega
theorem BSD_ap_p6971 : a_p 6971 = (82 : ℤ) := by
  have h := BSD_E143_card_p6971; unfold a_p; omega
theorem BSD_ap_p6977 : a_p 6977 = (135 : ℤ) := by
  have h := BSD_E143_card_p6977; unfold a_p; omega
theorem BSD_ap_p6983 : a_p 6983 = (-111 : ℤ) := by
  have h := BSD_E143_card_p6983; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6911: a_p=-8, 4p-a_p²=27580
theorem BSD_DegreeNonneg_p6911 : BSD_FrobeniusDegreeNonneg_OPEN 6911 := fun r => by
  have hap : (a_p 6911 : ℝ) = -8 := by exact_mod_cast BSD_ap_p6911
  have key : r ^ 2 - (a_p 6911 : ℝ) * r + ((6911 : ℕ) : ℝ) =
      (r + 8/2) ^ 2 + 27580/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (8 : ℝ)/2)]

-- p=6917: a_p=+38, 4p-a_p²=26224
theorem BSD_DegreeNonneg_p6917 : BSD_FrobeniusDegreeNonneg_OPEN 6917 := fun r => by
  have hap : (a_p 6917 : ℝ) = 38 := by exact_mod_cast BSD_ap_p6917
  have key : r ^ 2 - (a_p 6917 : ℝ) * r + ((6917 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 26224/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

-- p=6947: a_p=+66, 4p-a_p²=23432
theorem BSD_DegreeNonneg_p6947 : BSD_FrobeniusDegreeNonneg_OPEN 6947 := fun r => by
  have hap : (a_p 6947 : ℝ) = 66 := by exact_mod_cast BSD_ap_p6947
  have key : r ^ 2 - (a_p 6947 : ℝ) * r + ((6947 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 23432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

-- p=6949: a_p=-88, 4p-a_p²=20052
theorem BSD_DegreeNonneg_p6949 : BSD_FrobeniusDegreeNonneg_OPEN 6949 := fun r => by
  have hap : (a_p 6949 : ℝ) = -88 := by exact_mod_cast BSD_ap_p6949
  have key : r ^ 2 - (a_p 6949 : ℝ) * r + ((6949 : ℕ) : ℝ) =
      (r + 88/2) ^ 2 + 20052/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (88 : ℝ)/2)]

-- p=6959: a_p=-72, 4p-a_p²=22652
theorem BSD_DegreeNonneg_p6959 : BSD_FrobeniusDegreeNonneg_OPEN 6959 := fun r => by
  have hap : (a_p 6959 : ℝ) = -72 := by exact_mod_cast BSD_ap_p6959
  have key : r ^ 2 - (a_p 6959 : ℝ) * r + ((6959 : ℕ) : ℝ) =
      (r + 72/2) ^ 2 + 22652/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (72 : ℝ)/2)]

-- p=6961: a_p=-66, 4p-a_p²=23488
theorem BSD_DegreeNonneg_p6961 : BSD_FrobeniusDegreeNonneg_OPEN 6961 := fun r => by
  have hap : (a_p 6961 : ℝ) = -66 := by exact_mod_cast BSD_ap_p6961
  have key : r ^ 2 - (a_p 6961 : ℝ) * r + ((6961 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 23488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

-- p=6967: a_p=+16, 4p-a_p²=27612
theorem BSD_DegreeNonneg_p6967 : BSD_FrobeniusDegreeNonneg_OPEN 6967 := fun r => by
  have hap : (a_p 6967 : ℝ) = 16 := by exact_mod_cast BSD_ap_p6967
  have key : r ^ 2 - (a_p 6967 : ℝ) * r + ((6967 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 27612/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

-- p=6971: a_p=+82, 4p-a_p²=21160
theorem BSD_DegreeNonneg_p6971 : BSD_FrobeniusDegreeNonneg_OPEN 6971 := fun r => by
  have hap : (a_p 6971 : ℝ) = 82 := by exact_mod_cast BSD_ap_p6971
  have key : r ^ 2 - (a_p 6971 : ℝ) * r + ((6971 : ℕ) : ℝ) =
      (r - 82/2) ^ 2 + 21160/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (82 : ℝ)/2)]

-- p=6977: a_p=+135, 4p-a_p²=9683
theorem BSD_DegreeNonneg_p6977 : BSD_FrobeniusDegreeNonneg_OPEN 6977 := fun r => by
  have hap : (a_p 6977 : ℝ) = 135 := by exact_mod_cast BSD_ap_p6977
  have key : r ^ 2 - (a_p 6977 : ℝ) * r + ((6977 : ℕ) : ℝ) =
      (r - 135/2) ^ 2 + 9683/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (135 : ℝ)/2)]

-- p=6983: a_p=-111, 4p-a_p²=15611
theorem BSD_DegreeNonneg_p6983 : BSD_FrobeniusDegreeNonneg_OPEN 6983 := fun r => by
  have hap : (a_p 6983 : ℝ) = -111 := by exact_mod_cast BSD_ap_p6983
  have key : r ^ 2 - (a_p 6983 : ℝ) * r + ((6983 : ℕ) : ℝ) =
      (r + 111/2) ^ 2 + 15611/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (111 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6911 : BSD_Hasse_OPEN 6911 :=
  BSD_hasse_of_degree_nonneg 6911 BSD_DegreeNonneg_p6911
theorem BSD_Hasse_OPEN_p6917 : BSD_Hasse_OPEN 6917 :=
  BSD_hasse_of_degree_nonneg 6917 BSD_DegreeNonneg_p6917
theorem BSD_Hasse_OPEN_p6947 : BSD_Hasse_OPEN 6947 :=
  BSD_hasse_of_degree_nonneg 6947 BSD_DegreeNonneg_p6947
theorem BSD_Hasse_OPEN_p6949 : BSD_Hasse_OPEN 6949 :=
  BSD_hasse_of_degree_nonneg 6949 BSD_DegreeNonneg_p6949
theorem BSD_Hasse_OPEN_p6959 : BSD_Hasse_OPEN 6959 :=
  BSD_hasse_of_degree_nonneg 6959 BSD_DegreeNonneg_p6959
theorem BSD_Hasse_OPEN_p6961 : BSD_Hasse_OPEN 6961 :=
  BSD_hasse_of_degree_nonneg 6961 BSD_DegreeNonneg_p6961
theorem BSD_Hasse_OPEN_p6967 : BSD_Hasse_OPEN 6967 :=
  BSD_hasse_of_degree_nonneg 6967 BSD_DegreeNonneg_p6967
theorem BSD_Hasse_OPEN_p6971 : BSD_Hasse_OPEN 6971 :=
  BSD_hasse_of_degree_nonneg 6971 BSD_DegreeNonneg_p6971
theorem BSD_Hasse_OPEN_p6977 : BSD_Hasse_OPEN 6977 :=
  BSD_hasse_of_degree_nonneg 6977 BSD_DegreeNonneg_p6977
theorem BSD_Hasse_OPEN_p6983 : BSD_Hasse_OPEN 6983 :=
  BSD_hasse_of_degree_nonneg 6983 BSD_DegreeNonneg_p6983

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6911 : (a_p 6911 : ℝ) ^ 2 ≤ 4 * (6911 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6911
theorem BSD_HasseBound_Disc_p6917 : (a_p 6917 : ℝ) ^ 2 ≤ 4 * (6917 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6917
theorem BSD_HasseBound_Disc_p6947 : (a_p 6947 : ℝ) ^ 2 ≤ 4 * (6947 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6947
theorem BSD_HasseBound_Disc_p6949 : (a_p 6949 : ℝ) ^ 2 ≤ 4 * (6949 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6949
theorem BSD_HasseBound_Disc_p6959 : (a_p 6959 : ℝ) ^ 2 ≤ 4 * (6959 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6959
theorem BSD_HasseBound_Disc_p6961 : (a_p 6961 : ℝ) ^ 2 ≤ 4 * (6961 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6961
theorem BSD_HasseBound_Disc_p6967 : (a_p 6967 : ℝ) ^ 2 ≤ 4 * (6967 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6967
theorem BSD_HasseBound_Disc_p6971 : (a_p 6971 : ℝ) ^ 2 ≤ 4 * (6971 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6971
theorem BSD_HasseBound_Disc_p6977 : (a_p 6977 : ℝ) ^ 2 ≤ 4 * (6977 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6977
theorem BSD_HasseBound_Disc_p6983 : (a_p 6983 : ℝ) ^ 2 ≤ 4 * (6983 : ℝ) :=
  BSD_disc_from_deg_855 BSD_DegreeNonneg_p6983

end Towers.BSD