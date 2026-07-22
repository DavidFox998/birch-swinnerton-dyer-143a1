/-
================================================================
Towers / BSD / BSD_Genesis843_CLOSED  (genesis-843)

HasseBridge Tier C: Hasse bounds for primes
5851..5923 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5851: card=5970, a_p=-118, disc=-9480
  p=5857: card=5793, a_p=+65, disc=-19203
  p=5861: card=5868, a_p=-6, disc=-23408
  p=5867: card=5883, a_p=-15, disc=-23243
  p=5869: card=5950, a_p=-80, disc=-17076
  p=5879: card=5875, a_p=+5, disc=-23491
  p=5881: card=5834, a_p=+48, disc=-21220
  p=5897: card=5995, a_p=-97, disc=-14179
  p=5903: card=5930, a_p=-26, disc=-22936
  p=5923: card=5931, a_p=-7, disc=-23643

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_843 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i843_p5851 : Fact (5851 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5857 : Fact (5857 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5861 : Fact (5861 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5867 : Fact (5867 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5869 : Fact (5869 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5879 : Fact (5879 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5881 : Fact (5881 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5897 : Fact (5897 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5903 : Fact (5903 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5923 : Fact (5923 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5851 : (E143_Finset 5851).card = 5970 := by native_decide
theorem BSD_E143_card_p5857 : (E143_Finset 5857).card = 5793 := by native_decide
theorem BSD_E143_card_p5861 : (E143_Finset 5861).card = 5868 := by native_decide
theorem BSD_E143_card_p5867 : (E143_Finset 5867).card = 5883 := by native_decide
theorem BSD_E143_card_p5869 : (E143_Finset 5869).card = 5950 := by native_decide
theorem BSD_E143_card_p5879 : (E143_Finset 5879).card = 5875 := by native_decide
theorem BSD_E143_card_p5881 : (E143_Finset 5881).card = 5834 := by native_decide
theorem BSD_E143_card_p5897 : (E143_Finset 5897).card = 5995 := by native_decide
theorem BSD_E143_card_p5903 : (E143_Finset 5903).card = 5930 := by native_decide
theorem BSD_E143_card_p5923 : (E143_Finset 5923).card = 5931 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5851 : a_p 5851 = (-118 : ℤ) := by
  have h := BSD_E143_card_p5851; unfold a_p; omega
theorem BSD_ap_p5857 : a_p 5857 = (65 : ℤ) := by
  have h := BSD_E143_card_p5857; unfold a_p; omega
theorem BSD_ap_p5861 : a_p 5861 = (-6 : ℤ) := by
  have h := BSD_E143_card_p5861; unfold a_p; omega
theorem BSD_ap_p5867 : a_p 5867 = (-15 : ℤ) := by
  have h := BSD_E143_card_p5867; unfold a_p; omega
theorem BSD_ap_p5869 : a_p 5869 = (-80 : ℤ) := by
  have h := BSD_E143_card_p5869; unfold a_p; omega
theorem BSD_ap_p5879 : a_p 5879 = (5 : ℤ) := by
  have h := BSD_E143_card_p5879; unfold a_p; omega
theorem BSD_ap_p5881 : a_p 5881 = (48 : ℤ) := by
  have h := BSD_E143_card_p5881; unfold a_p; omega
theorem BSD_ap_p5897 : a_p 5897 = (-97 : ℤ) := by
  have h := BSD_E143_card_p5897; unfold a_p; omega
theorem BSD_ap_p5903 : a_p 5903 = (-26 : ℤ) := by
  have h := BSD_E143_card_p5903; unfold a_p; omega
theorem BSD_ap_p5923 : a_p 5923 = (-7 : ℤ) := by
  have h := BSD_E143_card_p5923; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5851: a_p=-118, 4p-a_p²=9480
theorem BSD_DegreeNonneg_p5851 : BSD_FrobeniusDegreeNonneg_OPEN 5851 := fun r => by
  have hap : (a_p 5851 : ℝ) = -118 := by exact_mod_cast BSD_ap_p5851
  have key : r ^ 2 - (a_p 5851 : ℝ) * r + ((5851 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 9480/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

-- p=5857: a_p=+65, 4p-a_p²=19203
theorem BSD_DegreeNonneg_p5857 : BSD_FrobeniusDegreeNonneg_OPEN 5857 := fun r => by
  have hap : (a_p 5857 : ℝ) = 65 := by exact_mod_cast BSD_ap_p5857
  have key : r ^ 2 - (a_p 5857 : ℝ) * r + ((5857 : ℕ) : ℝ) =
      (r - 65/2) ^ 2 + 19203/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (65 : ℝ)/2)]

-- p=5861: a_p=-6, 4p-a_p²=23408
theorem BSD_DegreeNonneg_p5861 : BSD_FrobeniusDegreeNonneg_OPEN 5861 := fun r => by
  have hap : (a_p 5861 : ℝ) = -6 := by exact_mod_cast BSD_ap_p5861
  have key : r ^ 2 - (a_p 5861 : ℝ) * r + ((5861 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 23408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

-- p=5867: a_p=-15, 4p-a_p²=23243
theorem BSD_DegreeNonneg_p5867 : BSD_FrobeniusDegreeNonneg_OPEN 5867 := fun r => by
  have hap : (a_p 5867 : ℝ) = -15 := by exact_mod_cast BSD_ap_p5867
  have key : r ^ 2 - (a_p 5867 : ℝ) * r + ((5867 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 23243/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

-- p=5869: a_p=-80, 4p-a_p²=17076
theorem BSD_DegreeNonneg_p5869 : BSD_FrobeniusDegreeNonneg_OPEN 5869 := fun r => by
  have hap : (a_p 5869 : ℝ) = -80 := by exact_mod_cast BSD_ap_p5869
  have key : r ^ 2 - (a_p 5869 : ℝ) * r + ((5869 : ℕ) : ℝ) =
      (r + 80/2) ^ 2 + 17076/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (80 : ℝ)/2)]

-- p=5879: a_p=+5, 4p-a_p²=23491
theorem BSD_DegreeNonneg_p5879 : BSD_FrobeniusDegreeNonneg_OPEN 5879 := fun r => by
  have hap : (a_p 5879 : ℝ) = 5 := by exact_mod_cast BSD_ap_p5879
  have key : r ^ 2 - (a_p 5879 : ℝ) * r + ((5879 : ℕ) : ℝ) =
      (r - 5/2) ^ 2 + 23491/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (5 : ℝ)/2)]

-- p=5881: a_p=+48, 4p-a_p²=21220
theorem BSD_DegreeNonneg_p5881 : BSD_FrobeniusDegreeNonneg_OPEN 5881 := fun r => by
  have hap : (a_p 5881 : ℝ) = 48 := by exact_mod_cast BSD_ap_p5881
  have key : r ^ 2 - (a_p 5881 : ℝ) * r + ((5881 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 21220/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

-- p=5897: a_p=-97, 4p-a_p²=14179
theorem BSD_DegreeNonneg_p5897 : BSD_FrobeniusDegreeNonneg_OPEN 5897 := fun r => by
  have hap : (a_p 5897 : ℝ) = -97 := by exact_mod_cast BSD_ap_p5897
  have key : r ^ 2 - (a_p 5897 : ℝ) * r + ((5897 : ℕ) : ℝ) =
      (r + 97/2) ^ 2 + 14179/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (97 : ℝ)/2)]

-- p=5903: a_p=-26, 4p-a_p²=22936
theorem BSD_DegreeNonneg_p5903 : BSD_FrobeniusDegreeNonneg_OPEN 5903 := fun r => by
  have hap : (a_p 5903 : ℝ) = -26 := by exact_mod_cast BSD_ap_p5903
  have key : r ^ 2 - (a_p 5903 : ℝ) * r + ((5903 : ℕ) : ℝ) =
      (r + 26/2) ^ 2 + 22936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (26 : ℝ)/2)]

-- p=5923: a_p=-7, 4p-a_p²=23643
theorem BSD_DegreeNonneg_p5923 : BSD_FrobeniusDegreeNonneg_OPEN 5923 := fun r => by
  have hap : (a_p 5923 : ℝ) = -7 := by exact_mod_cast BSD_ap_p5923
  have key : r ^ 2 - (a_p 5923 : ℝ) * r + ((5923 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 23643/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5851 : BSD_Hasse_OPEN 5851 :=
  BSD_hasse_of_degree_nonneg 5851 BSD_DegreeNonneg_p5851
theorem BSD_Hasse_OPEN_p5857 : BSD_Hasse_OPEN 5857 :=
  BSD_hasse_of_degree_nonneg 5857 BSD_DegreeNonneg_p5857
theorem BSD_Hasse_OPEN_p5861 : BSD_Hasse_OPEN 5861 :=
  BSD_hasse_of_degree_nonneg 5861 BSD_DegreeNonneg_p5861
theorem BSD_Hasse_OPEN_p5867 : BSD_Hasse_OPEN 5867 :=
  BSD_hasse_of_degree_nonneg 5867 BSD_DegreeNonneg_p5867
theorem BSD_Hasse_OPEN_p5869 : BSD_Hasse_OPEN 5869 :=
  BSD_hasse_of_degree_nonneg 5869 BSD_DegreeNonneg_p5869
theorem BSD_Hasse_OPEN_p5879 : BSD_Hasse_OPEN 5879 :=
  BSD_hasse_of_degree_nonneg 5879 BSD_DegreeNonneg_p5879
theorem BSD_Hasse_OPEN_p5881 : BSD_Hasse_OPEN 5881 :=
  BSD_hasse_of_degree_nonneg 5881 BSD_DegreeNonneg_p5881
theorem BSD_Hasse_OPEN_p5897 : BSD_Hasse_OPEN 5897 :=
  BSD_hasse_of_degree_nonneg 5897 BSD_DegreeNonneg_p5897
theorem BSD_Hasse_OPEN_p5903 : BSD_Hasse_OPEN 5903 :=
  BSD_hasse_of_degree_nonneg 5903 BSD_DegreeNonneg_p5903
theorem BSD_Hasse_OPEN_p5923 : BSD_Hasse_OPEN 5923 :=
  BSD_hasse_of_degree_nonneg 5923 BSD_DegreeNonneg_p5923

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5851 : (a_p 5851 : ℝ) ^ 2 ≤ 4 * (5851 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5851
theorem BSD_HasseBound_Disc_p5857 : (a_p 5857 : ℝ) ^ 2 ≤ 4 * (5857 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5857
theorem BSD_HasseBound_Disc_p5861 : (a_p 5861 : ℝ) ^ 2 ≤ 4 * (5861 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5861
theorem BSD_HasseBound_Disc_p5867 : (a_p 5867 : ℝ) ^ 2 ≤ 4 * (5867 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5867
theorem BSD_HasseBound_Disc_p5869 : (a_p 5869 : ℝ) ^ 2 ≤ 4 * (5869 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5869
theorem BSD_HasseBound_Disc_p5879 : (a_p 5879 : ℝ) ^ 2 ≤ 4 * (5879 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5879
theorem BSD_HasseBound_Disc_p5881 : (a_p 5881 : ℝ) ^ 2 ≤ 4 * (5881 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5881
theorem BSD_HasseBound_Disc_p5897 : (a_p 5897 : ℝ) ^ 2 ≤ 4 * (5897 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5897
theorem BSD_HasseBound_Disc_p5903 : (a_p 5903 : ℝ) ^ 2 ≤ 4 * (5903 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5903
theorem BSD_HasseBound_Disc_p5923 : (a_p 5923 : ℝ) ^ 2 ≤ 4 * (5923 : ℝ) :=
  BSD_disc_from_deg_843 BSD_DegreeNonneg_p5923

end Towers.BSD