/-
================================================================
Towers / BSD / BSD_Genesis784_CLOSED  (genesis-784)

HasseBridge Tier C: Hasse bounds for primes
1063..1123 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1063: card=1084, a_p=-20, disc=-3852
  p=1069: card=1038, a_p=+32, disc=-3252
  p=1087: card=1120, a_p=-32, disc=-3324
  p=1091: card=1080, a_p=+12, disc=-4220
  p=1093: card=1065, a_p=+29, disc=-3531
  p=1097: card=1160, a_p=-62, disc=-544
  p=1103: card=1097, a_p=+7, disc=-4363
  p=1109: card=1100, a_p=+10, disc=-4336
  p=1117: card=1106, a_p=+12, disc=-4324
  p=1123: card=1084, a_p=+40, disc=-2892

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_784 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i784_p1063 : Fact (1063 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1069 : Fact (1069 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1087 : Fact (1087 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1091 : Fact (1091 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1093 : Fact (1093 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1097 : Fact (1097 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1103 : Fact (1103 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1109 : Fact (1109 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1117 : Fact (1117 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1123 : Fact (1123 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1063 : (E143_Finset 1063).card = 1084 := by native_decide
theorem BSD_E143_card_p1069 : (E143_Finset 1069).card = 1038 := by native_decide
theorem BSD_E143_card_p1087 : (E143_Finset 1087).card = 1120 := by native_decide
theorem BSD_E143_card_p1091 : (E143_Finset 1091).card = 1080 := by native_decide
theorem BSD_E143_card_p1093 : (E143_Finset 1093).card = 1065 := by native_decide
theorem BSD_E143_card_p1097 : (E143_Finset 1097).card = 1160 := by native_decide
theorem BSD_E143_card_p1103 : (E143_Finset 1103).card = 1097 := by native_decide
theorem BSD_E143_card_p1109 : (E143_Finset 1109).card = 1100 := by native_decide
theorem BSD_E143_card_p1117 : (E143_Finset 1117).card = 1106 := by native_decide
theorem BSD_E143_card_p1123 : (E143_Finset 1123).card = 1084 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1063 : a_p 1063 = (-20 : ℤ) := by
  have h := BSD_E143_card_p1063; unfold a_p; omega
theorem BSD_ap_p1069 : a_p 1069 = (32 : ℤ) := by
  have h := BSD_E143_card_p1069; unfold a_p; omega
theorem BSD_ap_p1087 : a_p 1087 = (-32 : ℤ) := by
  have h := BSD_E143_card_p1087; unfold a_p; omega
theorem BSD_ap_p1091 : a_p 1091 = (12 : ℤ) := by
  have h := BSD_E143_card_p1091; unfold a_p; omega
theorem BSD_ap_p1093 : a_p 1093 = (29 : ℤ) := by
  have h := BSD_E143_card_p1093; unfold a_p; omega
theorem BSD_ap_p1097 : a_p 1097 = (-62 : ℤ) := by
  have h := BSD_E143_card_p1097; unfold a_p; omega
theorem BSD_ap_p1103 : a_p 1103 = (7 : ℤ) := by
  have h := BSD_E143_card_p1103; unfold a_p; omega
theorem BSD_ap_p1109 : a_p 1109 = (10 : ℤ) := by
  have h := BSD_E143_card_p1109; unfold a_p; omega
theorem BSD_ap_p1117 : a_p 1117 = (12 : ℤ) := by
  have h := BSD_E143_card_p1117; unfold a_p; omega
theorem BSD_ap_p1123 : a_p 1123 = (40 : ℤ) := by
  have h := BSD_E143_card_p1123; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1063: a_p=-20, 4p-a_p²=3852
theorem BSD_DegreeNonneg_p1063 : BSD_FrobeniusDegreeNonneg_OPEN 1063 := fun r => by
  have hap : (a_p 1063 : ℝ) = -20 := by exact_mod_cast BSD_ap_p1063
  have key : r ^ 2 - (a_p 1063 : ℝ) * r + ((1063 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 3852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=1069: a_p=+32, 4p-a_p²=3252
theorem BSD_DegreeNonneg_p1069 : BSD_FrobeniusDegreeNonneg_OPEN 1069 := fun r => by
  have hap : (a_p 1069 : ℝ) = 32 := by exact_mod_cast BSD_ap_p1069
  have key : r ^ 2 - (a_p 1069 : ℝ) * r + ((1069 : ℕ) : ℝ) =
      (r - 32/2) ^ 2 + 3252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (32 : ℝ)/2)]

-- p=1087: a_p=-32, 4p-a_p²=3324
theorem BSD_DegreeNonneg_p1087 : BSD_FrobeniusDegreeNonneg_OPEN 1087 := fun r => by
  have hap : (a_p 1087 : ℝ) = -32 := by exact_mod_cast BSD_ap_p1087
  have key : r ^ 2 - (a_p 1087 : ℝ) * r + ((1087 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 3324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=1091: a_p=+12, 4p-a_p²=4220
theorem BSD_DegreeNonneg_p1091 : BSD_FrobeniusDegreeNonneg_OPEN 1091 := fun r => by
  have hap : (a_p 1091 : ℝ) = 12 := by exact_mod_cast BSD_ap_p1091
  have key : r ^ 2 - (a_p 1091 : ℝ) * r + ((1091 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 4220/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=1093: a_p=+29, 4p-a_p²=3531
theorem BSD_DegreeNonneg_p1093 : BSD_FrobeniusDegreeNonneg_OPEN 1093 := fun r => by
  have hap : (a_p 1093 : ℝ) = 29 := by exact_mod_cast BSD_ap_p1093
  have key : r ^ 2 - (a_p 1093 : ℝ) * r + ((1093 : ℕ) : ℝ) =
      (r - 29/2) ^ 2 + 3531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (29 : ℝ)/2)]

-- p=1097: a_p=-62, 4p-a_p²=544
theorem BSD_DegreeNonneg_p1097 : BSD_FrobeniusDegreeNonneg_OPEN 1097 := fun r => by
  have hap : (a_p 1097 : ℝ) = -62 := by exact_mod_cast BSD_ap_p1097
  have key : r ^ 2 - (a_p 1097 : ℝ) * r + ((1097 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

-- p=1103: a_p=+7, 4p-a_p²=4363
theorem BSD_DegreeNonneg_p1103 : BSD_FrobeniusDegreeNonneg_OPEN 1103 := fun r => by
  have hap : (a_p 1103 : ℝ) = 7 := by exact_mod_cast BSD_ap_p1103
  have key : r ^ 2 - (a_p 1103 : ℝ) * r + ((1103 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 4363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

-- p=1109: a_p=+10, 4p-a_p²=4336
theorem BSD_DegreeNonneg_p1109 : BSD_FrobeniusDegreeNonneg_OPEN 1109 := fun r => by
  have hap : (a_p 1109 : ℝ) = 10 := by exact_mod_cast BSD_ap_p1109
  have key : r ^ 2 - (a_p 1109 : ℝ) * r + ((1109 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 4336/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

-- p=1117: a_p=+12, 4p-a_p²=4324
theorem BSD_DegreeNonneg_p1117 : BSD_FrobeniusDegreeNonneg_OPEN 1117 := fun r => by
  have hap : (a_p 1117 : ℝ) = 12 := by exact_mod_cast BSD_ap_p1117
  have key : r ^ 2 - (a_p 1117 : ℝ) * r + ((1117 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 4324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=1123: a_p=+40, 4p-a_p²=2892
theorem BSD_DegreeNonneg_p1123 : BSD_FrobeniusDegreeNonneg_OPEN 1123 := fun r => by
  have hap : (a_p 1123 : ℝ) = 40 := by exact_mod_cast BSD_ap_p1123
  have key : r ^ 2 - (a_p 1123 : ℝ) * r + ((1123 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 2892/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1063 : BSD_Hasse_OPEN 1063 :=
  BSD_hasse_of_degree_nonneg 1063 BSD_DegreeNonneg_p1063
theorem BSD_Hasse_OPEN_p1069 : BSD_Hasse_OPEN 1069 :=
  BSD_hasse_of_degree_nonneg 1069 BSD_DegreeNonneg_p1069
theorem BSD_Hasse_OPEN_p1087 : BSD_Hasse_OPEN 1087 :=
  BSD_hasse_of_degree_nonneg 1087 BSD_DegreeNonneg_p1087
theorem BSD_Hasse_OPEN_p1091 : BSD_Hasse_OPEN 1091 :=
  BSD_hasse_of_degree_nonneg 1091 BSD_DegreeNonneg_p1091
theorem BSD_Hasse_OPEN_p1093 : BSD_Hasse_OPEN 1093 :=
  BSD_hasse_of_degree_nonneg 1093 BSD_DegreeNonneg_p1093
theorem BSD_Hasse_OPEN_p1097 : BSD_Hasse_OPEN 1097 :=
  BSD_hasse_of_degree_nonneg 1097 BSD_DegreeNonneg_p1097
theorem BSD_Hasse_OPEN_p1103 : BSD_Hasse_OPEN 1103 :=
  BSD_hasse_of_degree_nonneg 1103 BSD_DegreeNonneg_p1103
theorem BSD_Hasse_OPEN_p1109 : BSD_Hasse_OPEN 1109 :=
  BSD_hasse_of_degree_nonneg 1109 BSD_DegreeNonneg_p1109
theorem BSD_Hasse_OPEN_p1117 : BSD_Hasse_OPEN 1117 :=
  BSD_hasse_of_degree_nonneg 1117 BSD_DegreeNonneg_p1117
theorem BSD_Hasse_OPEN_p1123 : BSD_Hasse_OPEN 1123 :=
  BSD_hasse_of_degree_nonneg 1123 BSD_DegreeNonneg_p1123

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1063 : (a_p 1063 : ℝ) ^ 2 ≤ 4 * (1063 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1063
theorem BSD_HasseBound_Disc_p1069 : (a_p 1069 : ℝ) ^ 2 ≤ 4 * (1069 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1069
theorem BSD_HasseBound_Disc_p1087 : (a_p 1087 : ℝ) ^ 2 ≤ 4 * (1087 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1087
theorem BSD_HasseBound_Disc_p1091 : (a_p 1091 : ℝ) ^ 2 ≤ 4 * (1091 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1091
theorem BSD_HasseBound_Disc_p1093 : (a_p 1093 : ℝ) ^ 2 ≤ 4 * (1093 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1093
theorem BSD_HasseBound_Disc_p1097 : (a_p 1097 : ℝ) ^ 2 ≤ 4 * (1097 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1097
theorem BSD_HasseBound_Disc_p1103 : (a_p 1103 : ℝ) ^ 2 ≤ 4 * (1103 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1103
theorem BSD_HasseBound_Disc_p1109 : (a_p 1109 : ℝ) ^ 2 ≤ 4 * (1109 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1109
theorem BSD_HasseBound_Disc_p1117 : (a_p 1117 : ℝ) ^ 2 ≤ 4 * (1117 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1117
theorem BSD_HasseBound_Disc_p1123 : (a_p 1123 : ℝ) ^ 2 ≤ 4 * (1123 : ℝ) :=
  BSD_disc_from_deg_784 BSD_DegreeNonneg_p1123

end Towers.BSD