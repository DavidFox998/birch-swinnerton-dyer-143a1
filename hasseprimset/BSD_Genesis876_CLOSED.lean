/-
================================================================
Towers / BSD / BSD_Genesis876_CLOSED  (genesis-876)

HasseBridge Tier C: Hasse bounds for primes
8821..8893 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8821: card=8812, a_p=+10, disc=-35184
  p=8831: card=8875, a_p=-43, disc=-33475
  p=8837: card=8679, a_p=+159, disc=-10067
  p=8839: card=8822, a_p=+18, disc=-35032
  p=8849: card=8856, a_p=-6, disc=-35360
  p=8861: card=8790, a_p=+72, disc=-30260
  p=8863: card=8812, a_p=+52, disc=-32748
  p=8867: card=8821, a_p=+47, disc=-33259
  p=8887: card=9020, a_p=-132, disc=-18124
  p=8893: card=8748, a_p=+146, disc=-14256

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_876 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i876_p8821 : Fact (8821 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8831 : Fact (8831 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8837 : Fact (8837 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8839 : Fact (8839 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8849 : Fact (8849 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8861 : Fact (8861 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8863 : Fact (8863 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8867 : Fact (8867 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8887 : Fact (8887 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8893 : Fact (8893 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8821 : (E143_Finset 8821).card = 8812 := by native_decide
theorem BSD_E143_card_p8831 : (E143_Finset 8831).card = 8875 := by native_decide
theorem BSD_E143_card_p8837 : (E143_Finset 8837).card = 8679 := by native_decide
theorem BSD_E143_card_p8839 : (E143_Finset 8839).card = 8822 := by native_decide
theorem BSD_E143_card_p8849 : (E143_Finset 8849).card = 8856 := by native_decide
theorem BSD_E143_card_p8861 : (E143_Finset 8861).card = 8790 := by native_decide
theorem BSD_E143_card_p8863 : (E143_Finset 8863).card = 8812 := by native_decide
theorem BSD_E143_card_p8867 : (E143_Finset 8867).card = 8821 := by native_decide
theorem BSD_E143_card_p8887 : (E143_Finset 8887).card = 9020 := by native_decide
theorem BSD_E143_card_p8893 : (E143_Finset 8893).card = 8748 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8821 : a_p 8821 = (10 : ℤ) := by
  have h := BSD_E143_card_p8821; unfold a_p; omega
theorem BSD_ap_p8831 : a_p 8831 = (-43 : ℤ) := by
  have h := BSD_E143_card_p8831; unfold a_p; omega
theorem BSD_ap_p8837 : a_p 8837 = (159 : ℤ) := by
  have h := BSD_E143_card_p8837; unfold a_p; omega
theorem BSD_ap_p8839 : a_p 8839 = (18 : ℤ) := by
  have h := BSD_E143_card_p8839; unfold a_p; omega
theorem BSD_ap_p8849 : a_p 8849 = (-6 : ℤ) := by
  have h := BSD_E143_card_p8849; unfold a_p; omega
theorem BSD_ap_p8861 : a_p 8861 = (72 : ℤ) := by
  have h := BSD_E143_card_p8861; unfold a_p; omega
theorem BSD_ap_p8863 : a_p 8863 = (52 : ℤ) := by
  have h := BSD_E143_card_p8863; unfold a_p; omega
theorem BSD_ap_p8867 : a_p 8867 = (47 : ℤ) := by
  have h := BSD_E143_card_p8867; unfold a_p; omega
theorem BSD_ap_p8887 : a_p 8887 = (-132 : ℤ) := by
  have h := BSD_E143_card_p8887; unfold a_p; omega
theorem BSD_ap_p8893 : a_p 8893 = (146 : ℤ) := by
  have h := BSD_E143_card_p8893; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8821: a_p=+10, 4p-a_p²=35184
theorem BSD_DegreeNonneg_p8821 : BSD_FrobeniusDegreeNonneg_OPEN 8821 := fun r => by
  have hap : (a_p 8821 : ℝ) = 10 := by exact_mod_cast BSD_ap_p8821
  have key : r ^ 2 - (a_p 8821 : ℝ) * r + ((8821 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 35184/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

-- p=8831: a_p=-43, 4p-a_p²=33475
theorem BSD_DegreeNonneg_p8831 : BSD_FrobeniusDegreeNonneg_OPEN 8831 := fun r => by
  have hap : (a_p 8831 : ℝ) = -43 := by exact_mod_cast BSD_ap_p8831
  have key : r ^ 2 - (a_p 8831 : ℝ) * r + ((8831 : ℕ) : ℝ) =
      (r + 43/2) ^ 2 + 33475/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (43 : ℝ)/2)]

-- p=8837: a_p=+159, 4p-a_p²=10067
theorem BSD_DegreeNonneg_p8837 : BSD_FrobeniusDegreeNonneg_OPEN 8837 := fun r => by
  have hap : (a_p 8837 : ℝ) = 159 := by exact_mod_cast BSD_ap_p8837
  have key : r ^ 2 - (a_p 8837 : ℝ) * r + ((8837 : ℕ) : ℝ) =
      (r - 159/2) ^ 2 + 10067/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (159 : ℝ)/2)]

-- p=8839: a_p=+18, 4p-a_p²=35032
theorem BSD_DegreeNonneg_p8839 : BSD_FrobeniusDegreeNonneg_OPEN 8839 := fun r => by
  have hap : (a_p 8839 : ℝ) = 18 := by exact_mod_cast BSD_ap_p8839
  have key : r ^ 2 - (a_p 8839 : ℝ) * r + ((8839 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 35032/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=8849: a_p=-6, 4p-a_p²=35360
theorem BSD_DegreeNonneg_p8849 : BSD_FrobeniusDegreeNonneg_OPEN 8849 := fun r => by
  have hap : (a_p 8849 : ℝ) = -6 := by exact_mod_cast BSD_ap_p8849
  have key : r ^ 2 - (a_p 8849 : ℝ) * r + ((8849 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 35360/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

-- p=8861: a_p=+72, 4p-a_p²=30260
theorem BSD_DegreeNonneg_p8861 : BSD_FrobeniusDegreeNonneg_OPEN 8861 := fun r => by
  have hap : (a_p 8861 : ℝ) = 72 := by exact_mod_cast BSD_ap_p8861
  have key : r ^ 2 - (a_p 8861 : ℝ) * r + ((8861 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 30260/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

-- p=8863: a_p=+52, 4p-a_p²=32748
theorem BSD_DegreeNonneg_p8863 : BSD_FrobeniusDegreeNonneg_OPEN 8863 := fun r => by
  have hap : (a_p 8863 : ℝ) = 52 := by exact_mod_cast BSD_ap_p8863
  have key : r ^ 2 - (a_p 8863 : ℝ) * r + ((8863 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 32748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

-- p=8867: a_p=+47, 4p-a_p²=33259
theorem BSD_DegreeNonneg_p8867 : BSD_FrobeniusDegreeNonneg_OPEN 8867 := fun r => by
  have hap : (a_p 8867 : ℝ) = 47 := by exact_mod_cast BSD_ap_p8867
  have key : r ^ 2 - (a_p 8867 : ℝ) * r + ((8867 : ℕ) : ℝ) =
      (r - 47/2) ^ 2 + 33259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (47 : ℝ)/2)]

-- p=8887: a_p=-132, 4p-a_p²=18124
theorem BSD_DegreeNonneg_p8887 : BSD_FrobeniusDegreeNonneg_OPEN 8887 := fun r => by
  have hap : (a_p 8887 : ℝ) = -132 := by exact_mod_cast BSD_ap_p8887
  have key : r ^ 2 - (a_p 8887 : ℝ) * r + ((8887 : ℕ) : ℝ) =
      (r + 132/2) ^ 2 + 18124/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (132 : ℝ)/2)]

-- p=8893: a_p=+146, 4p-a_p²=14256
theorem BSD_DegreeNonneg_p8893 : BSD_FrobeniusDegreeNonneg_OPEN 8893 := fun r => by
  have hap : (a_p 8893 : ℝ) = 146 := by exact_mod_cast BSD_ap_p8893
  have key : r ^ 2 - (a_p 8893 : ℝ) * r + ((8893 : ℕ) : ℝ) =
      (r - 146/2) ^ 2 + 14256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (146 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8821 : BSD_Hasse_OPEN 8821 :=
  BSD_hasse_of_degree_nonneg 8821 BSD_DegreeNonneg_p8821
theorem BSD_Hasse_OPEN_p8831 : BSD_Hasse_OPEN 8831 :=
  BSD_hasse_of_degree_nonneg 8831 BSD_DegreeNonneg_p8831
theorem BSD_Hasse_OPEN_p8837 : BSD_Hasse_OPEN 8837 :=
  BSD_hasse_of_degree_nonneg 8837 BSD_DegreeNonneg_p8837
theorem BSD_Hasse_OPEN_p8839 : BSD_Hasse_OPEN 8839 :=
  BSD_hasse_of_degree_nonneg 8839 BSD_DegreeNonneg_p8839
theorem BSD_Hasse_OPEN_p8849 : BSD_Hasse_OPEN 8849 :=
  BSD_hasse_of_degree_nonneg 8849 BSD_DegreeNonneg_p8849
theorem BSD_Hasse_OPEN_p8861 : BSD_Hasse_OPEN 8861 :=
  BSD_hasse_of_degree_nonneg 8861 BSD_DegreeNonneg_p8861
theorem BSD_Hasse_OPEN_p8863 : BSD_Hasse_OPEN 8863 :=
  BSD_hasse_of_degree_nonneg 8863 BSD_DegreeNonneg_p8863
theorem BSD_Hasse_OPEN_p8867 : BSD_Hasse_OPEN 8867 :=
  BSD_hasse_of_degree_nonneg 8867 BSD_DegreeNonneg_p8867
theorem BSD_Hasse_OPEN_p8887 : BSD_Hasse_OPEN 8887 :=
  BSD_hasse_of_degree_nonneg 8887 BSD_DegreeNonneg_p8887
theorem BSD_Hasse_OPEN_p8893 : BSD_Hasse_OPEN 8893 :=
  BSD_hasse_of_degree_nonneg 8893 BSD_DegreeNonneg_p8893

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8821 : (a_p 8821 : ℝ) ^ 2 ≤ 4 * (8821 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8821
theorem BSD_HasseBound_Disc_p8831 : (a_p 8831 : ℝ) ^ 2 ≤ 4 * (8831 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8831
theorem BSD_HasseBound_Disc_p8837 : (a_p 8837 : ℝ) ^ 2 ≤ 4 * (8837 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8837
theorem BSD_HasseBound_Disc_p8839 : (a_p 8839 : ℝ) ^ 2 ≤ 4 * (8839 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8839
theorem BSD_HasseBound_Disc_p8849 : (a_p 8849 : ℝ) ^ 2 ≤ 4 * (8849 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8849
theorem BSD_HasseBound_Disc_p8861 : (a_p 8861 : ℝ) ^ 2 ≤ 4 * (8861 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8861
theorem BSD_HasseBound_Disc_p8863 : (a_p 8863 : ℝ) ^ 2 ≤ 4 * (8863 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8863
theorem BSD_HasseBound_Disc_p8867 : (a_p 8867 : ℝ) ^ 2 ≤ 4 * (8867 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8867
theorem BSD_HasseBound_Disc_p8887 : (a_p 8887 : ℝ) ^ 2 ≤ 4 * (8887 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8887
theorem BSD_HasseBound_Disc_p8893 : (a_p 8893 : ℝ) ^ 2 ≤ 4 * (8893 : ℝ) :=
  BSD_disc_from_deg_876 BSD_DegreeNonneg_p8893

end Towers.BSD