/-
================================================================
Towers / BSD / BSD_Genesis879_CLOSED  (genesis-879)

HasseBridge Tier C: Hasse bounds for primes
9103..9181 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9103: card=9170, a_p=-66, disc=-32056
  p=9109: card=9165, a_p=-55, disc=-33411
  p=9127: card=9238, a_p=-110, disc=-24408
  p=9133: card=9241, a_p=-107, disc=-25083
  p=9137: card=9188, a_p=-50, disc=-34048
  p=9151: card=9122, a_p=+30, disc=-35704
  p=9157: card=9053, a_p=+105, disc=-25603
  p=9161: card=9052, a_p=+110, disc=-24544
  p=9173: card=9064, a_p=+110, disc=-24592
  p=9181: card=9332, a_p=-150, disc=-14224

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_879 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i879_p9103 : Fact (9103 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9109 : Fact (9109 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9127 : Fact (9127 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9133 : Fact (9133 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9137 : Fact (9137 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9151 : Fact (9151 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9157 : Fact (9157 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9161 : Fact (9161 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9173 : Fact (9173 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9181 : Fact (9181 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9103 : (E143_Finset 9103).card = 9170 := by native_decide
theorem BSD_E143_card_p9109 : (E143_Finset 9109).card = 9165 := by native_decide
theorem BSD_E143_card_p9127 : (E143_Finset 9127).card = 9238 := by native_decide
theorem BSD_E143_card_p9133 : (E143_Finset 9133).card = 9241 := by native_decide
theorem BSD_E143_card_p9137 : (E143_Finset 9137).card = 9188 := by native_decide
theorem BSD_E143_card_p9151 : (E143_Finset 9151).card = 9122 := by native_decide
theorem BSD_E143_card_p9157 : (E143_Finset 9157).card = 9053 := by native_decide
theorem BSD_E143_card_p9161 : (E143_Finset 9161).card = 9052 := by native_decide
theorem BSD_E143_card_p9173 : (E143_Finset 9173).card = 9064 := by native_decide
theorem BSD_E143_card_p9181 : (E143_Finset 9181).card = 9332 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9103 : a_p 9103 = (-66 : ℤ) := by
  have h := BSD_E143_card_p9103; unfold a_p; omega
theorem BSD_ap_p9109 : a_p 9109 = (-55 : ℤ) := by
  have h := BSD_E143_card_p9109; unfold a_p; omega
theorem BSD_ap_p9127 : a_p 9127 = (-110 : ℤ) := by
  have h := BSD_E143_card_p9127; unfold a_p; omega
theorem BSD_ap_p9133 : a_p 9133 = (-107 : ℤ) := by
  have h := BSD_E143_card_p9133; unfold a_p; omega
theorem BSD_ap_p9137 : a_p 9137 = (-50 : ℤ) := by
  have h := BSD_E143_card_p9137; unfold a_p; omega
theorem BSD_ap_p9151 : a_p 9151 = (30 : ℤ) := by
  have h := BSD_E143_card_p9151; unfold a_p; omega
theorem BSD_ap_p9157 : a_p 9157 = (105 : ℤ) := by
  have h := BSD_E143_card_p9157; unfold a_p; omega
theorem BSD_ap_p9161 : a_p 9161 = (110 : ℤ) := by
  have h := BSD_E143_card_p9161; unfold a_p; omega
theorem BSD_ap_p9173 : a_p 9173 = (110 : ℤ) := by
  have h := BSD_E143_card_p9173; unfold a_p; omega
theorem BSD_ap_p9181 : a_p 9181 = (-150 : ℤ) := by
  have h := BSD_E143_card_p9181; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9103: a_p=-66, 4p-a_p²=32056
theorem BSD_DegreeNonneg_p9103 : BSD_FrobeniusDegreeNonneg_OPEN 9103 := fun r => by
  have hap : (a_p 9103 : ℝ) = -66 := by exact_mod_cast BSD_ap_p9103
  have key : r ^ 2 - (a_p 9103 : ℝ) * r + ((9103 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 32056/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

-- p=9109: a_p=-55, 4p-a_p²=33411
theorem BSD_DegreeNonneg_p9109 : BSD_FrobeniusDegreeNonneg_OPEN 9109 := fun r => by
  have hap : (a_p 9109 : ℝ) = -55 := by exact_mod_cast BSD_ap_p9109
  have key : r ^ 2 - (a_p 9109 : ℝ) * r + ((9109 : ℕ) : ℝ) =
      (r + 55/2) ^ 2 + 33411/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (55 : ℝ)/2)]

-- p=9127: a_p=-110, 4p-a_p²=24408
theorem BSD_DegreeNonneg_p9127 : BSD_FrobeniusDegreeNonneg_OPEN 9127 := fun r => by
  have hap : (a_p 9127 : ℝ) = -110 := by exact_mod_cast BSD_ap_p9127
  have key : r ^ 2 - (a_p 9127 : ℝ) * r + ((9127 : ℕ) : ℝ) =
      (r + 110/2) ^ 2 + 24408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (110 : ℝ)/2)]

-- p=9133: a_p=-107, 4p-a_p²=25083
theorem BSD_DegreeNonneg_p9133 : BSD_FrobeniusDegreeNonneg_OPEN 9133 := fun r => by
  have hap : (a_p 9133 : ℝ) = -107 := by exact_mod_cast BSD_ap_p9133
  have key : r ^ 2 - (a_p 9133 : ℝ) * r + ((9133 : ℕ) : ℝ) =
      (r + 107/2) ^ 2 + 25083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (107 : ℝ)/2)]

-- p=9137: a_p=-50, 4p-a_p²=34048
theorem BSD_DegreeNonneg_p9137 : BSD_FrobeniusDegreeNonneg_OPEN 9137 := fun r => by
  have hap : (a_p 9137 : ℝ) = -50 := by exact_mod_cast BSD_ap_p9137
  have key : r ^ 2 - (a_p 9137 : ℝ) * r + ((9137 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 34048/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

-- p=9151: a_p=+30, 4p-a_p²=35704
theorem BSD_DegreeNonneg_p9151 : BSD_FrobeniusDegreeNonneg_OPEN 9151 := fun r => by
  have hap : (a_p 9151 : ℝ) = 30 := by exact_mod_cast BSD_ap_p9151
  have key : r ^ 2 - (a_p 9151 : ℝ) * r + ((9151 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 35704/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

-- p=9157: a_p=+105, 4p-a_p²=25603
theorem BSD_DegreeNonneg_p9157 : BSD_FrobeniusDegreeNonneg_OPEN 9157 := fun r => by
  have hap : (a_p 9157 : ℝ) = 105 := by exact_mod_cast BSD_ap_p9157
  have key : r ^ 2 - (a_p 9157 : ℝ) * r + ((9157 : ℕ) : ℝ) =
      (r - 105/2) ^ 2 + 25603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (105 : ℝ)/2)]

-- p=9161: a_p=+110, 4p-a_p²=24544
theorem BSD_DegreeNonneg_p9161 : BSD_FrobeniusDegreeNonneg_OPEN 9161 := fun r => by
  have hap : (a_p 9161 : ℝ) = 110 := by exact_mod_cast BSD_ap_p9161
  have key : r ^ 2 - (a_p 9161 : ℝ) * r + ((9161 : ℕ) : ℝ) =
      (r - 110/2) ^ 2 + 24544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (110 : ℝ)/2)]

-- p=9173: a_p=+110, 4p-a_p²=24592
theorem BSD_DegreeNonneg_p9173 : BSD_FrobeniusDegreeNonneg_OPEN 9173 := fun r => by
  have hap : (a_p 9173 : ℝ) = 110 := by exact_mod_cast BSD_ap_p9173
  have key : r ^ 2 - (a_p 9173 : ℝ) * r + ((9173 : ℕ) : ℝ) =
      (r - 110/2) ^ 2 + 24592/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (110 : ℝ)/2)]

-- p=9181: a_p=-150, 4p-a_p²=14224
theorem BSD_DegreeNonneg_p9181 : BSD_FrobeniusDegreeNonneg_OPEN 9181 := fun r => by
  have hap : (a_p 9181 : ℝ) = -150 := by exact_mod_cast BSD_ap_p9181
  have key : r ^ 2 - (a_p 9181 : ℝ) * r + ((9181 : ℕ) : ℝ) =
      (r + 150/2) ^ 2 + 14224/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (150 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9103 : BSD_Hasse_OPEN 9103 :=
  BSD_hasse_of_degree_nonneg 9103 BSD_DegreeNonneg_p9103
theorem BSD_Hasse_OPEN_p9109 : BSD_Hasse_OPEN 9109 :=
  BSD_hasse_of_degree_nonneg 9109 BSD_DegreeNonneg_p9109
theorem BSD_Hasse_OPEN_p9127 : BSD_Hasse_OPEN 9127 :=
  BSD_hasse_of_degree_nonneg 9127 BSD_DegreeNonneg_p9127
theorem BSD_Hasse_OPEN_p9133 : BSD_Hasse_OPEN 9133 :=
  BSD_hasse_of_degree_nonneg 9133 BSD_DegreeNonneg_p9133
theorem BSD_Hasse_OPEN_p9137 : BSD_Hasse_OPEN 9137 :=
  BSD_hasse_of_degree_nonneg 9137 BSD_DegreeNonneg_p9137
theorem BSD_Hasse_OPEN_p9151 : BSD_Hasse_OPEN 9151 :=
  BSD_hasse_of_degree_nonneg 9151 BSD_DegreeNonneg_p9151
theorem BSD_Hasse_OPEN_p9157 : BSD_Hasse_OPEN 9157 :=
  BSD_hasse_of_degree_nonneg 9157 BSD_DegreeNonneg_p9157
theorem BSD_Hasse_OPEN_p9161 : BSD_Hasse_OPEN 9161 :=
  BSD_hasse_of_degree_nonneg 9161 BSD_DegreeNonneg_p9161
theorem BSD_Hasse_OPEN_p9173 : BSD_Hasse_OPEN 9173 :=
  BSD_hasse_of_degree_nonneg 9173 BSD_DegreeNonneg_p9173
theorem BSD_Hasse_OPEN_p9181 : BSD_Hasse_OPEN 9181 :=
  BSD_hasse_of_degree_nonneg 9181 BSD_DegreeNonneg_p9181

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9103 : (a_p 9103 : ℝ) ^ 2 ≤ 4 * (9103 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9103
theorem BSD_HasseBound_Disc_p9109 : (a_p 9109 : ℝ) ^ 2 ≤ 4 * (9109 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9109
theorem BSD_HasseBound_Disc_p9127 : (a_p 9127 : ℝ) ^ 2 ≤ 4 * (9127 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9127
theorem BSD_HasseBound_Disc_p9133 : (a_p 9133 : ℝ) ^ 2 ≤ 4 * (9133 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9133
theorem BSD_HasseBound_Disc_p9137 : (a_p 9137 : ℝ) ^ 2 ≤ 4 * (9137 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9137
theorem BSD_HasseBound_Disc_p9151 : (a_p 9151 : ℝ) ^ 2 ≤ 4 * (9151 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9151
theorem BSD_HasseBound_Disc_p9157 : (a_p 9157 : ℝ) ^ 2 ≤ 4 * (9157 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9157
theorem BSD_HasseBound_Disc_p9161 : (a_p 9161 : ℝ) ^ 2 ≤ 4 * (9161 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9161
theorem BSD_HasseBound_Disc_p9173 : (a_p 9173 : ℝ) ^ 2 ≤ 4 * (9173 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9173
theorem BSD_HasseBound_Disc_p9181 : (a_p 9181 : ℝ) ^ 2 ≤ 4 * (9181 : ℝ) :=
  BSD_disc_from_deg_879 BSD_DegreeNonneg_p9181

end Towers.BSD