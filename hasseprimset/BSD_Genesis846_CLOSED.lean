/-
================================================================
Towers / BSD / BSD_Genesis846_CLOSED  (genesis-846)

HasseBridge Tier C: Hasse bounds for primes
6131..6211 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6131: card=6137, a_p=-5, disc=-24499
  p=6133: card=6150, a_p=-16, disc=-24276
  p=6143: card=6052, a_p=+92, disc=-16108
  p=6151: card=6114, a_p=+38, disc=-23160
  p=6163: card=6085, a_p=+79, disc=-18411
  p=6173: card=6160, a_p=+14, disc=-24496
  p=6197: card=6297, a_p=-99, disc=-14987
  p=6199: card=6148, a_p=+52, disc=-22092
  p=6203: card=6188, a_p=+16, disc=-24556
  p=6211: card=6232, a_p=-20, disc=-24444

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_846 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i846_p6131 : Fact (6131 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6133 : Fact (6133 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6143 : Fact (6143 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6151 : Fact (6151 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6163 : Fact (6163 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6173 : Fact (6173 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6197 : Fact (6197 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6199 : Fact (6199 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6203 : Fact (6203 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6211 : Fact (6211 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6131 : (E143_Finset 6131).card = 6137 := by native_decide
theorem BSD_E143_card_p6133 : (E143_Finset 6133).card = 6150 := by native_decide
theorem BSD_E143_card_p6143 : (E143_Finset 6143).card = 6052 := by native_decide
theorem BSD_E143_card_p6151 : (E143_Finset 6151).card = 6114 := by native_decide
theorem BSD_E143_card_p6163 : (E143_Finset 6163).card = 6085 := by native_decide
theorem BSD_E143_card_p6173 : (E143_Finset 6173).card = 6160 := by native_decide
theorem BSD_E143_card_p6197 : (E143_Finset 6197).card = 6297 := by native_decide
theorem BSD_E143_card_p6199 : (E143_Finset 6199).card = 6148 := by native_decide
theorem BSD_E143_card_p6203 : (E143_Finset 6203).card = 6188 := by native_decide
theorem BSD_E143_card_p6211 : (E143_Finset 6211).card = 6232 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6131 : a_p 6131 = (-5 : ℤ) := by
  have h := BSD_E143_card_p6131; unfold a_p; omega
theorem BSD_ap_p6133 : a_p 6133 = (-16 : ℤ) := by
  have h := BSD_E143_card_p6133; unfold a_p; omega
theorem BSD_ap_p6143 : a_p 6143 = (92 : ℤ) := by
  have h := BSD_E143_card_p6143; unfold a_p; omega
theorem BSD_ap_p6151 : a_p 6151 = (38 : ℤ) := by
  have h := BSD_E143_card_p6151; unfold a_p; omega
theorem BSD_ap_p6163 : a_p 6163 = (79 : ℤ) := by
  have h := BSD_E143_card_p6163; unfold a_p; omega
theorem BSD_ap_p6173 : a_p 6173 = (14 : ℤ) := by
  have h := BSD_E143_card_p6173; unfold a_p; omega
theorem BSD_ap_p6197 : a_p 6197 = (-99 : ℤ) := by
  have h := BSD_E143_card_p6197; unfold a_p; omega
theorem BSD_ap_p6199 : a_p 6199 = (52 : ℤ) := by
  have h := BSD_E143_card_p6199; unfold a_p; omega
theorem BSD_ap_p6203 : a_p 6203 = (16 : ℤ) := by
  have h := BSD_E143_card_p6203; unfold a_p; omega
theorem BSD_ap_p6211 : a_p 6211 = (-20 : ℤ) := by
  have h := BSD_E143_card_p6211; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6131: a_p=-5, 4p-a_p²=24499
theorem BSD_DegreeNonneg_p6131 : BSD_FrobeniusDegreeNonneg_OPEN 6131 := fun r => by
  have hap : (a_p 6131 : ℝ) = -5 := by exact_mod_cast BSD_ap_p6131
  have key : r ^ 2 - (a_p 6131 : ℝ) * r + ((6131 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 24499/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

-- p=6133: a_p=-16, 4p-a_p²=24276
theorem BSD_DegreeNonneg_p6133 : BSD_FrobeniusDegreeNonneg_OPEN 6133 := fun r => by
  have hap : (a_p 6133 : ℝ) = -16 := by exact_mod_cast BSD_ap_p6133
  have key : r ^ 2 - (a_p 6133 : ℝ) * r + ((6133 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 24276/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

-- p=6143: a_p=+92, 4p-a_p²=16108
theorem BSD_DegreeNonneg_p6143 : BSD_FrobeniusDegreeNonneg_OPEN 6143 := fun r => by
  have hap : (a_p 6143 : ℝ) = 92 := by exact_mod_cast BSD_ap_p6143
  have key : r ^ 2 - (a_p 6143 : ℝ) * r + ((6143 : ℕ) : ℝ) =
      (r - 92/2) ^ 2 + 16108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (92 : ℝ)/2)]

-- p=6151: a_p=+38, 4p-a_p²=23160
theorem BSD_DegreeNonneg_p6151 : BSD_FrobeniusDegreeNonneg_OPEN 6151 := fun r => by
  have hap : (a_p 6151 : ℝ) = 38 := by exact_mod_cast BSD_ap_p6151
  have key : r ^ 2 - (a_p 6151 : ℝ) * r + ((6151 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 23160/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

-- p=6163: a_p=+79, 4p-a_p²=18411
theorem BSD_DegreeNonneg_p6163 : BSD_FrobeniusDegreeNonneg_OPEN 6163 := fun r => by
  have hap : (a_p 6163 : ℝ) = 79 := by exact_mod_cast BSD_ap_p6163
  have key : r ^ 2 - (a_p 6163 : ℝ) * r + ((6163 : ℕ) : ℝ) =
      (r - 79/2) ^ 2 + 18411/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (79 : ℝ)/2)]

-- p=6173: a_p=+14, 4p-a_p²=24496
theorem BSD_DegreeNonneg_p6173 : BSD_FrobeniusDegreeNonneg_OPEN 6173 := fun r => by
  have hap : (a_p 6173 : ℝ) = 14 := by exact_mod_cast BSD_ap_p6173
  have key : r ^ 2 - (a_p 6173 : ℝ) * r + ((6173 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 24496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

-- p=6197: a_p=-99, 4p-a_p²=14987
theorem BSD_DegreeNonneg_p6197 : BSD_FrobeniusDegreeNonneg_OPEN 6197 := fun r => by
  have hap : (a_p 6197 : ℝ) = -99 := by exact_mod_cast BSD_ap_p6197
  have key : r ^ 2 - (a_p 6197 : ℝ) * r + ((6197 : ℕ) : ℝ) =
      (r + 99/2) ^ 2 + 14987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (99 : ℝ)/2)]

-- p=6199: a_p=+52, 4p-a_p²=22092
theorem BSD_DegreeNonneg_p6199 : BSD_FrobeniusDegreeNonneg_OPEN 6199 := fun r => by
  have hap : (a_p 6199 : ℝ) = 52 := by exact_mod_cast BSD_ap_p6199
  have key : r ^ 2 - (a_p 6199 : ℝ) * r + ((6199 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 22092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

-- p=6203: a_p=+16, 4p-a_p²=24556
theorem BSD_DegreeNonneg_p6203 : BSD_FrobeniusDegreeNonneg_OPEN 6203 := fun r => by
  have hap : (a_p 6203 : ℝ) = 16 := by exact_mod_cast BSD_ap_p6203
  have key : r ^ 2 - (a_p 6203 : ℝ) * r + ((6203 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 24556/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

-- p=6211: a_p=-20, 4p-a_p²=24444
theorem BSD_DegreeNonneg_p6211 : BSD_FrobeniusDegreeNonneg_OPEN 6211 := fun r => by
  have hap : (a_p 6211 : ℝ) = -20 := by exact_mod_cast BSD_ap_p6211
  have key : r ^ 2 - (a_p 6211 : ℝ) * r + ((6211 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 24444/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6131 : BSD_Hasse_OPEN 6131 :=
  BSD_hasse_of_degree_nonneg 6131 BSD_DegreeNonneg_p6131
theorem BSD_Hasse_OPEN_p6133 : BSD_Hasse_OPEN 6133 :=
  BSD_hasse_of_degree_nonneg 6133 BSD_DegreeNonneg_p6133
theorem BSD_Hasse_OPEN_p6143 : BSD_Hasse_OPEN 6143 :=
  BSD_hasse_of_degree_nonneg 6143 BSD_DegreeNonneg_p6143
theorem BSD_Hasse_OPEN_p6151 : BSD_Hasse_OPEN 6151 :=
  BSD_hasse_of_degree_nonneg 6151 BSD_DegreeNonneg_p6151
theorem BSD_Hasse_OPEN_p6163 : BSD_Hasse_OPEN 6163 :=
  BSD_hasse_of_degree_nonneg 6163 BSD_DegreeNonneg_p6163
theorem BSD_Hasse_OPEN_p6173 : BSD_Hasse_OPEN 6173 :=
  BSD_hasse_of_degree_nonneg 6173 BSD_DegreeNonneg_p6173
theorem BSD_Hasse_OPEN_p6197 : BSD_Hasse_OPEN 6197 :=
  BSD_hasse_of_degree_nonneg 6197 BSD_DegreeNonneg_p6197
theorem BSD_Hasse_OPEN_p6199 : BSD_Hasse_OPEN 6199 :=
  BSD_hasse_of_degree_nonneg 6199 BSD_DegreeNonneg_p6199
theorem BSD_Hasse_OPEN_p6203 : BSD_Hasse_OPEN 6203 :=
  BSD_hasse_of_degree_nonneg 6203 BSD_DegreeNonneg_p6203
theorem BSD_Hasse_OPEN_p6211 : BSD_Hasse_OPEN 6211 :=
  BSD_hasse_of_degree_nonneg 6211 BSD_DegreeNonneg_p6211

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6131 : (a_p 6131 : ℝ) ^ 2 ≤ 4 * (6131 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6131
theorem BSD_HasseBound_Disc_p6133 : (a_p 6133 : ℝ) ^ 2 ≤ 4 * (6133 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6133
theorem BSD_HasseBound_Disc_p6143 : (a_p 6143 : ℝ) ^ 2 ≤ 4 * (6143 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6143
theorem BSD_HasseBound_Disc_p6151 : (a_p 6151 : ℝ) ^ 2 ≤ 4 * (6151 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6151
theorem BSD_HasseBound_Disc_p6163 : (a_p 6163 : ℝ) ^ 2 ≤ 4 * (6163 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6163
theorem BSD_HasseBound_Disc_p6173 : (a_p 6173 : ℝ) ^ 2 ≤ 4 * (6173 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6173
theorem BSD_HasseBound_Disc_p6197 : (a_p 6197 : ℝ) ^ 2 ≤ 4 * (6197 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6197
theorem BSD_HasseBound_Disc_p6199 : (a_p 6199 : ℝ) ^ 2 ≤ 4 * (6199 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6199
theorem BSD_HasseBound_Disc_p6203 : (a_p 6203 : ℝ) ^ 2 ≤ 4 * (6203 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6203
theorem BSD_HasseBound_Disc_p6211 : (a_p 6211 : ℝ) ^ 2 ≤ 4 * (6211 : ℝ) :=
  BSD_disc_from_deg_846 BSD_DegreeNonneg_p6211

end Towers.BSD