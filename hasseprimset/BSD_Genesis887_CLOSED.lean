/-
================================================================
Towers / BSD / BSD_Genesis887_CLOSED  (genesis-887)

HasseBridge Tier C: Hasse bounds for primes
9803..9871 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9803: card=9828, a_p=-24, disc=-38636
  p=9811: card=9830, a_p=-18, disc=-38920
  p=9817: card=9728, a_p=+90, disc=-31168
  p=9829: card=9816, a_p=+14, disc=-39120
  p=9833: card=9828, a_p=+6, disc=-39296
  p=9839: card=9851, a_p=-11, disc=-39235
  p=9851: card=9918, a_p=-66, disc=-35048
  p=9857: card=10031, a_p=-173, disc=-9499
  p=9859: card=9883, a_p=-23, disc=-38907
  p=9871: card=9888, a_p=-16, disc=-39228

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_887 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i887_p9803 : Fact (9803 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9811 : Fact (9811 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9817 : Fact (9817 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9829 : Fact (9829 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9833 : Fact (9833 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9839 : Fact (9839 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9851 : Fact (9851 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9857 : Fact (9857 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9859 : Fact (9859 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9871 : Fact (9871 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9803 : (E143_Finset 9803).card = 9828 := by native_decide
theorem BSD_E143_card_p9811 : (E143_Finset 9811).card = 9830 := by native_decide
theorem BSD_E143_card_p9817 : (E143_Finset 9817).card = 9728 := by native_decide
theorem BSD_E143_card_p9829 : (E143_Finset 9829).card = 9816 := by native_decide
theorem BSD_E143_card_p9833 : (E143_Finset 9833).card = 9828 := by native_decide
theorem BSD_E143_card_p9839 : (E143_Finset 9839).card = 9851 := by native_decide
theorem BSD_E143_card_p9851 : (E143_Finset 9851).card = 9918 := by native_decide
theorem BSD_E143_card_p9857 : (E143_Finset 9857).card = 10031 := by native_decide
theorem BSD_E143_card_p9859 : (E143_Finset 9859).card = 9883 := by native_decide
theorem BSD_E143_card_p9871 : (E143_Finset 9871).card = 9888 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9803 : a_p 9803 = (-24 : ℤ) := by
  have h := BSD_E143_card_p9803; unfold a_p; omega
theorem BSD_ap_p9811 : a_p 9811 = (-18 : ℤ) := by
  have h := BSD_E143_card_p9811; unfold a_p; omega
theorem BSD_ap_p9817 : a_p 9817 = (90 : ℤ) := by
  have h := BSD_E143_card_p9817; unfold a_p; omega
theorem BSD_ap_p9829 : a_p 9829 = (14 : ℤ) := by
  have h := BSD_E143_card_p9829; unfold a_p; omega
theorem BSD_ap_p9833 : a_p 9833 = (6 : ℤ) := by
  have h := BSD_E143_card_p9833; unfold a_p; omega
theorem BSD_ap_p9839 : a_p 9839 = (-11 : ℤ) := by
  have h := BSD_E143_card_p9839; unfold a_p; omega
theorem BSD_ap_p9851 : a_p 9851 = (-66 : ℤ) := by
  have h := BSD_E143_card_p9851; unfold a_p; omega
theorem BSD_ap_p9857 : a_p 9857 = (-173 : ℤ) := by
  have h := BSD_E143_card_p9857; unfold a_p; omega
theorem BSD_ap_p9859 : a_p 9859 = (-23 : ℤ) := by
  have h := BSD_E143_card_p9859; unfold a_p; omega
theorem BSD_ap_p9871 : a_p 9871 = (-16 : ℤ) := by
  have h := BSD_E143_card_p9871; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9803: a_p=-24, 4p-a_p²=38636
theorem BSD_DegreeNonneg_p9803 : BSD_FrobeniusDegreeNonneg_OPEN 9803 := fun r => by
  have hap : (a_p 9803 : ℝ) = -24 := by exact_mod_cast BSD_ap_p9803
  have key : r ^ 2 - (a_p 9803 : ℝ) * r + ((9803 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 38636/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=9811: a_p=-18, 4p-a_p²=38920
theorem BSD_DegreeNonneg_p9811 : BSD_FrobeniusDegreeNonneg_OPEN 9811 := fun r => by
  have hap : (a_p 9811 : ℝ) = -18 := by exact_mod_cast BSD_ap_p9811
  have key : r ^ 2 - (a_p 9811 : ℝ) * r + ((9811 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 38920/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

-- p=9817: a_p=+90, 4p-a_p²=31168
theorem BSD_DegreeNonneg_p9817 : BSD_FrobeniusDegreeNonneg_OPEN 9817 := fun r => by
  have hap : (a_p 9817 : ℝ) = 90 := by exact_mod_cast BSD_ap_p9817
  have key : r ^ 2 - (a_p 9817 : ℝ) * r + ((9817 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 31168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

-- p=9829: a_p=+14, 4p-a_p²=39120
theorem BSD_DegreeNonneg_p9829 : BSD_FrobeniusDegreeNonneg_OPEN 9829 := fun r => by
  have hap : (a_p 9829 : ℝ) = 14 := by exact_mod_cast BSD_ap_p9829
  have key : r ^ 2 - (a_p 9829 : ℝ) * r + ((9829 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 39120/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

-- p=9833: a_p=+6, 4p-a_p²=39296
theorem BSD_DegreeNonneg_p9833 : BSD_FrobeniusDegreeNonneg_OPEN 9833 := fun r => by
  have hap : (a_p 9833 : ℝ) = 6 := by exact_mod_cast BSD_ap_p9833
  have key : r ^ 2 - (a_p 9833 : ℝ) * r + ((9833 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 39296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

-- p=9839: a_p=-11, 4p-a_p²=39235
theorem BSD_DegreeNonneg_p9839 : BSD_FrobeniusDegreeNonneg_OPEN 9839 := fun r => by
  have hap : (a_p 9839 : ℝ) = -11 := by exact_mod_cast BSD_ap_p9839
  have key : r ^ 2 - (a_p 9839 : ℝ) * r + ((9839 : ℕ) : ℝ) =
      (r + 11/2) ^ 2 + 39235/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (11 : ℝ)/2)]

-- p=9851: a_p=-66, 4p-a_p²=35048
theorem BSD_DegreeNonneg_p9851 : BSD_FrobeniusDegreeNonneg_OPEN 9851 := fun r => by
  have hap : (a_p 9851 : ℝ) = -66 := by exact_mod_cast BSD_ap_p9851
  have key : r ^ 2 - (a_p 9851 : ℝ) * r + ((9851 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 35048/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

-- p=9857: a_p=-173, 4p-a_p²=9499
theorem BSD_DegreeNonneg_p9857 : BSD_FrobeniusDegreeNonneg_OPEN 9857 := fun r => by
  have hap : (a_p 9857 : ℝ) = -173 := by exact_mod_cast BSD_ap_p9857
  have key : r ^ 2 - (a_p 9857 : ℝ) * r + ((9857 : ℕ) : ℝ) =
      (r + 173/2) ^ 2 + 9499/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (173 : ℝ)/2)]

-- p=9859: a_p=-23, 4p-a_p²=38907
theorem BSD_DegreeNonneg_p9859 : BSD_FrobeniusDegreeNonneg_OPEN 9859 := fun r => by
  have hap : (a_p 9859 : ℝ) = -23 := by exact_mod_cast BSD_ap_p9859
  have key : r ^ 2 - (a_p 9859 : ℝ) * r + ((9859 : ℕ) : ℝ) =
      (r + 23/2) ^ 2 + 38907/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (23 : ℝ)/2)]

-- p=9871: a_p=-16, 4p-a_p²=39228
theorem BSD_DegreeNonneg_p9871 : BSD_FrobeniusDegreeNonneg_OPEN 9871 := fun r => by
  have hap : (a_p 9871 : ℝ) = -16 := by exact_mod_cast BSD_ap_p9871
  have key : r ^ 2 - (a_p 9871 : ℝ) * r + ((9871 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 39228/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9803 : BSD_Hasse_OPEN 9803 :=
  BSD_hasse_of_degree_nonneg 9803 BSD_DegreeNonneg_p9803
theorem BSD_Hasse_OPEN_p9811 : BSD_Hasse_OPEN 9811 :=
  BSD_hasse_of_degree_nonneg 9811 BSD_DegreeNonneg_p9811
theorem BSD_Hasse_OPEN_p9817 : BSD_Hasse_OPEN 9817 :=
  BSD_hasse_of_degree_nonneg 9817 BSD_DegreeNonneg_p9817
theorem BSD_Hasse_OPEN_p9829 : BSD_Hasse_OPEN 9829 :=
  BSD_hasse_of_degree_nonneg 9829 BSD_DegreeNonneg_p9829
theorem BSD_Hasse_OPEN_p9833 : BSD_Hasse_OPEN 9833 :=
  BSD_hasse_of_degree_nonneg 9833 BSD_DegreeNonneg_p9833
theorem BSD_Hasse_OPEN_p9839 : BSD_Hasse_OPEN 9839 :=
  BSD_hasse_of_degree_nonneg 9839 BSD_DegreeNonneg_p9839
theorem BSD_Hasse_OPEN_p9851 : BSD_Hasse_OPEN 9851 :=
  BSD_hasse_of_degree_nonneg 9851 BSD_DegreeNonneg_p9851
theorem BSD_Hasse_OPEN_p9857 : BSD_Hasse_OPEN 9857 :=
  BSD_hasse_of_degree_nonneg 9857 BSD_DegreeNonneg_p9857
theorem BSD_Hasse_OPEN_p9859 : BSD_Hasse_OPEN 9859 :=
  BSD_hasse_of_degree_nonneg 9859 BSD_DegreeNonneg_p9859
theorem BSD_Hasse_OPEN_p9871 : BSD_Hasse_OPEN 9871 :=
  BSD_hasse_of_degree_nonneg 9871 BSD_DegreeNonneg_p9871

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9803 : (a_p 9803 : ℝ) ^ 2 ≤ 4 * (9803 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9803
theorem BSD_HasseBound_Disc_p9811 : (a_p 9811 : ℝ) ^ 2 ≤ 4 * (9811 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9811
theorem BSD_HasseBound_Disc_p9817 : (a_p 9817 : ℝ) ^ 2 ≤ 4 * (9817 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9817
theorem BSD_HasseBound_Disc_p9829 : (a_p 9829 : ℝ) ^ 2 ≤ 4 * (9829 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9829
theorem BSD_HasseBound_Disc_p9833 : (a_p 9833 : ℝ) ^ 2 ≤ 4 * (9833 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9833
theorem BSD_HasseBound_Disc_p9839 : (a_p 9839 : ℝ) ^ 2 ≤ 4 * (9839 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9839
theorem BSD_HasseBound_Disc_p9851 : (a_p 9851 : ℝ) ^ 2 ≤ 4 * (9851 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9851
theorem BSD_HasseBound_Disc_p9857 : (a_p 9857 : ℝ) ^ 2 ≤ 4 * (9857 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9857
theorem BSD_HasseBound_Disc_p9859 : (a_p 9859 : ℝ) ^ 2 ≤ 4 * (9859 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9859
theorem BSD_HasseBound_Disc_p9871 : (a_p 9871 : ℝ) ^ 2 ≤ 4 * (9871 : ℝ) :=
  BSD_disc_from_deg_887 BSD_DegreeNonneg_p9871

end Towers.BSD