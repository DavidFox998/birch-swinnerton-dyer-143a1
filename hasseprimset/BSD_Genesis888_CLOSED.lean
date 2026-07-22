/-
================================================================
Towers / BSD / BSD_Genesis888_CLOSED  (genesis-888)

HasseBridge Tier C: Hasse bounds for primes
9883..9967 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9883: card=9833, a_p=+51, disc=-36931
  p=9887: card=9915, a_p=-27, disc=-38819
  p=9901: card=10020, a_p=-118, disc=-25680
  p=9907: card=9846, a_p=+62, disc=-35784
  p=9923: card=9795, a_p=+129, disc=-23051
  p=9929: card=10076, a_p=-146, disc=-18400
  p=9931: card=10015, a_p=-83, disc=-32835
  p=9941: card=9870, a_p=+72, disc=-34580
  p=9949: card=9848, a_p=+102, disc=-29392
  p=9967: card=9865, a_p=+103, disc=-29259

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_888 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i888_p9883 : Fact (9883 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9887 : Fact (9887 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9901 : Fact (9901 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9907 : Fact (9907 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9923 : Fact (9923 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9929 : Fact (9929 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9931 : Fact (9931 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9941 : Fact (9941 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9949 : Fact (9949 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9967 : Fact (9967 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9883 : (E143_Finset 9883).card = 9833 := by native_decide
theorem BSD_E143_card_p9887 : (E143_Finset 9887).card = 9915 := by native_decide
theorem BSD_E143_card_p9901 : (E143_Finset 9901).card = 10020 := by native_decide
theorem BSD_E143_card_p9907 : (E143_Finset 9907).card = 9846 := by native_decide
theorem BSD_E143_card_p9923 : (E143_Finset 9923).card = 9795 := by native_decide
theorem BSD_E143_card_p9929 : (E143_Finset 9929).card = 10076 := by native_decide
theorem BSD_E143_card_p9931 : (E143_Finset 9931).card = 10015 := by native_decide
theorem BSD_E143_card_p9941 : (E143_Finset 9941).card = 9870 := by native_decide
theorem BSD_E143_card_p9949 : (E143_Finset 9949).card = 9848 := by native_decide
theorem BSD_E143_card_p9967 : (E143_Finset 9967).card = 9865 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9883 : a_p 9883 = (51 : ℤ) := by
  have h := BSD_E143_card_p9883; unfold a_p; omega
theorem BSD_ap_p9887 : a_p 9887 = (-27 : ℤ) := by
  have h := BSD_E143_card_p9887; unfold a_p; omega
theorem BSD_ap_p9901 : a_p 9901 = (-118 : ℤ) := by
  have h := BSD_E143_card_p9901; unfold a_p; omega
theorem BSD_ap_p9907 : a_p 9907 = (62 : ℤ) := by
  have h := BSD_E143_card_p9907; unfold a_p; omega
theorem BSD_ap_p9923 : a_p 9923 = (129 : ℤ) := by
  have h := BSD_E143_card_p9923; unfold a_p; omega
theorem BSD_ap_p9929 : a_p 9929 = (-146 : ℤ) := by
  have h := BSD_E143_card_p9929; unfold a_p; omega
theorem BSD_ap_p9931 : a_p 9931 = (-83 : ℤ) := by
  have h := BSD_E143_card_p9931; unfold a_p; omega
theorem BSD_ap_p9941 : a_p 9941 = (72 : ℤ) := by
  have h := BSD_E143_card_p9941; unfold a_p; omega
theorem BSD_ap_p9949 : a_p 9949 = (102 : ℤ) := by
  have h := BSD_E143_card_p9949; unfold a_p; omega
theorem BSD_ap_p9967 : a_p 9967 = (103 : ℤ) := by
  have h := BSD_E143_card_p9967; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9883: a_p=+51, 4p-a_p²=36931
theorem BSD_DegreeNonneg_p9883 : BSD_FrobeniusDegreeNonneg_OPEN 9883 := fun r => by
  have hap : (a_p 9883 : ℝ) = 51 := by exact_mod_cast BSD_ap_p9883
  have key : r ^ 2 - (a_p 9883 : ℝ) * r + ((9883 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 36931/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

-- p=9887: a_p=-27, 4p-a_p²=38819
theorem BSD_DegreeNonneg_p9887 : BSD_FrobeniusDegreeNonneg_OPEN 9887 := fun r => by
  have hap : (a_p 9887 : ℝ) = -27 := by exact_mod_cast BSD_ap_p9887
  have key : r ^ 2 - (a_p 9887 : ℝ) * r + ((9887 : ℕ) : ℝ) =
      (r + 27/2) ^ 2 + 38819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (27 : ℝ)/2)]

-- p=9901: a_p=-118, 4p-a_p²=25680
theorem BSD_DegreeNonneg_p9901 : BSD_FrobeniusDegreeNonneg_OPEN 9901 := fun r => by
  have hap : (a_p 9901 : ℝ) = -118 := by exact_mod_cast BSD_ap_p9901
  have key : r ^ 2 - (a_p 9901 : ℝ) * r + ((9901 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 25680/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

-- p=9907: a_p=+62, 4p-a_p²=35784
theorem BSD_DegreeNonneg_p9907 : BSD_FrobeniusDegreeNonneg_OPEN 9907 := fun r => by
  have hap : (a_p 9907 : ℝ) = 62 := by exact_mod_cast BSD_ap_p9907
  have key : r ^ 2 - (a_p 9907 : ℝ) * r + ((9907 : ℕ) : ℝ) =
      (r - 62/2) ^ 2 + 35784/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (62 : ℝ)/2)]

-- p=9923: a_p=+129, 4p-a_p²=23051
theorem BSD_DegreeNonneg_p9923 : BSD_FrobeniusDegreeNonneg_OPEN 9923 := fun r => by
  have hap : (a_p 9923 : ℝ) = 129 := by exact_mod_cast BSD_ap_p9923
  have key : r ^ 2 - (a_p 9923 : ℝ) * r + ((9923 : ℕ) : ℝ) =
      (r - 129/2) ^ 2 + 23051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (129 : ℝ)/2)]

-- p=9929: a_p=-146, 4p-a_p²=18400
theorem BSD_DegreeNonneg_p9929 : BSD_FrobeniusDegreeNonneg_OPEN 9929 := fun r => by
  have hap : (a_p 9929 : ℝ) = -146 := by exact_mod_cast BSD_ap_p9929
  have key : r ^ 2 - (a_p 9929 : ℝ) * r + ((9929 : ℕ) : ℝ) =
      (r + 146/2) ^ 2 + 18400/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (146 : ℝ)/2)]

-- p=9931: a_p=-83, 4p-a_p²=32835
theorem BSD_DegreeNonneg_p9931 : BSD_FrobeniusDegreeNonneg_OPEN 9931 := fun r => by
  have hap : (a_p 9931 : ℝ) = -83 := by exact_mod_cast BSD_ap_p9931
  have key : r ^ 2 - (a_p 9931 : ℝ) * r + ((9931 : ℕ) : ℝ) =
      (r + 83/2) ^ 2 + 32835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (83 : ℝ)/2)]

-- p=9941: a_p=+72, 4p-a_p²=34580
theorem BSD_DegreeNonneg_p9941 : BSD_FrobeniusDegreeNonneg_OPEN 9941 := fun r => by
  have hap : (a_p 9941 : ℝ) = 72 := by exact_mod_cast BSD_ap_p9941
  have key : r ^ 2 - (a_p 9941 : ℝ) * r + ((9941 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 34580/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

-- p=9949: a_p=+102, 4p-a_p²=29392
theorem BSD_DegreeNonneg_p9949 : BSD_FrobeniusDegreeNonneg_OPEN 9949 := fun r => by
  have hap : (a_p 9949 : ℝ) = 102 := by exact_mod_cast BSD_ap_p9949
  have key : r ^ 2 - (a_p 9949 : ℝ) * r + ((9949 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 29392/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

-- p=9967: a_p=+103, 4p-a_p²=29259
theorem BSD_DegreeNonneg_p9967 : BSD_FrobeniusDegreeNonneg_OPEN 9967 := fun r => by
  have hap : (a_p 9967 : ℝ) = 103 := by exact_mod_cast BSD_ap_p9967
  have key : r ^ 2 - (a_p 9967 : ℝ) * r + ((9967 : ℕ) : ℝ) =
      (r - 103/2) ^ 2 + 29259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (103 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9883 : BSD_Hasse_OPEN 9883 :=
  BSD_hasse_of_degree_nonneg 9883 BSD_DegreeNonneg_p9883
theorem BSD_Hasse_OPEN_p9887 : BSD_Hasse_OPEN 9887 :=
  BSD_hasse_of_degree_nonneg 9887 BSD_DegreeNonneg_p9887
theorem BSD_Hasse_OPEN_p9901 : BSD_Hasse_OPEN 9901 :=
  BSD_hasse_of_degree_nonneg 9901 BSD_DegreeNonneg_p9901
theorem BSD_Hasse_OPEN_p9907 : BSD_Hasse_OPEN 9907 :=
  BSD_hasse_of_degree_nonneg 9907 BSD_DegreeNonneg_p9907
theorem BSD_Hasse_OPEN_p9923 : BSD_Hasse_OPEN 9923 :=
  BSD_hasse_of_degree_nonneg 9923 BSD_DegreeNonneg_p9923
theorem BSD_Hasse_OPEN_p9929 : BSD_Hasse_OPEN 9929 :=
  BSD_hasse_of_degree_nonneg 9929 BSD_DegreeNonneg_p9929
theorem BSD_Hasse_OPEN_p9931 : BSD_Hasse_OPEN 9931 :=
  BSD_hasse_of_degree_nonneg 9931 BSD_DegreeNonneg_p9931
theorem BSD_Hasse_OPEN_p9941 : BSD_Hasse_OPEN 9941 :=
  BSD_hasse_of_degree_nonneg 9941 BSD_DegreeNonneg_p9941
theorem BSD_Hasse_OPEN_p9949 : BSD_Hasse_OPEN 9949 :=
  BSD_hasse_of_degree_nonneg 9949 BSD_DegreeNonneg_p9949
theorem BSD_Hasse_OPEN_p9967 : BSD_Hasse_OPEN 9967 :=
  BSD_hasse_of_degree_nonneg 9967 BSD_DegreeNonneg_p9967

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9883 : (a_p 9883 : ℝ) ^ 2 ≤ 4 * (9883 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9883
theorem BSD_HasseBound_Disc_p9887 : (a_p 9887 : ℝ) ^ 2 ≤ 4 * (9887 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9887
theorem BSD_HasseBound_Disc_p9901 : (a_p 9901 : ℝ) ^ 2 ≤ 4 * (9901 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9901
theorem BSD_HasseBound_Disc_p9907 : (a_p 9907 : ℝ) ^ 2 ≤ 4 * (9907 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9907
theorem BSD_HasseBound_Disc_p9923 : (a_p 9923 : ℝ) ^ 2 ≤ 4 * (9923 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9923
theorem BSD_HasseBound_Disc_p9929 : (a_p 9929 : ℝ) ^ 2 ≤ 4 * (9929 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9929
theorem BSD_HasseBound_Disc_p9931 : (a_p 9931 : ℝ) ^ 2 ≤ 4 * (9931 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9931
theorem BSD_HasseBound_Disc_p9941 : (a_p 9941 : ℝ) ^ 2 ≤ 4 * (9941 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9941
theorem BSD_HasseBound_Disc_p9949 : (a_p 9949 : ℝ) ^ 2 ≤ 4 * (9949 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9949
theorem BSD_HasseBound_Disc_p9967 : (a_p 9967 : ℝ) ^ 2 ≤ 4 * (9967 : ℝ) :=
  BSD_disc_from_deg_888 BSD_DegreeNonneg_p9967

end Towers.BSD