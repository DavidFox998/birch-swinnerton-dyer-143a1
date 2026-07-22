/-
================================================================
Towers / BSD / BSD_Genesis878_CLOSED  (genesis-878)

HasseBridge Tier C: Hasse bounds for primes
9007..9091 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9007: card=8865, a_p=+143, disc=-15579
  p=9011: card=8916, a_p=+96, disc=-26828
  p=9013: card=8947, a_p=+67, disc=-31563
  p=9029: card=8925, a_p=+105, disc=-25091
  p=9041: card=9054, a_p=-12, disc=-36020
  p=9043: card=9176, a_p=-132, disc=-18748
  p=9049: card=9006, a_p=+44, disc=-34260
  p=9059: card=9114, a_p=-54, disc=-33320
  p=9067: card=9133, a_p=-65, disc=-32043
  p=9091: card=8929, a_p=+163, disc=-9795

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_878 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i878_p9007 : Fact (9007 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9011 : Fact (9011 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9013 : Fact (9013 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9029 : Fact (9029 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9041 : Fact (9041 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9043 : Fact (9043 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9049 : Fact (9049 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9059 : Fact (9059 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9067 : Fact (9067 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9091 : Fact (9091 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9007 : (E143_Finset 9007).card = 8865 := by native_decide
theorem BSD_E143_card_p9011 : (E143_Finset 9011).card = 8916 := by native_decide
theorem BSD_E143_card_p9013 : (E143_Finset 9013).card = 8947 := by native_decide
theorem BSD_E143_card_p9029 : (E143_Finset 9029).card = 8925 := by native_decide
theorem BSD_E143_card_p9041 : (E143_Finset 9041).card = 9054 := by native_decide
theorem BSD_E143_card_p9043 : (E143_Finset 9043).card = 9176 := by native_decide
theorem BSD_E143_card_p9049 : (E143_Finset 9049).card = 9006 := by native_decide
theorem BSD_E143_card_p9059 : (E143_Finset 9059).card = 9114 := by native_decide
theorem BSD_E143_card_p9067 : (E143_Finset 9067).card = 9133 := by native_decide
theorem BSD_E143_card_p9091 : (E143_Finset 9091).card = 8929 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9007 : a_p 9007 = (143 : ℤ) := by
  have h := BSD_E143_card_p9007; unfold a_p; omega
theorem BSD_ap_p9011 : a_p 9011 = (96 : ℤ) := by
  have h := BSD_E143_card_p9011; unfold a_p; omega
theorem BSD_ap_p9013 : a_p 9013 = (67 : ℤ) := by
  have h := BSD_E143_card_p9013; unfold a_p; omega
theorem BSD_ap_p9029 : a_p 9029 = (105 : ℤ) := by
  have h := BSD_E143_card_p9029; unfold a_p; omega
theorem BSD_ap_p9041 : a_p 9041 = (-12 : ℤ) := by
  have h := BSD_E143_card_p9041; unfold a_p; omega
theorem BSD_ap_p9043 : a_p 9043 = (-132 : ℤ) := by
  have h := BSD_E143_card_p9043; unfold a_p; omega
theorem BSD_ap_p9049 : a_p 9049 = (44 : ℤ) := by
  have h := BSD_E143_card_p9049; unfold a_p; omega
theorem BSD_ap_p9059 : a_p 9059 = (-54 : ℤ) := by
  have h := BSD_E143_card_p9059; unfold a_p; omega
theorem BSD_ap_p9067 : a_p 9067 = (-65 : ℤ) := by
  have h := BSD_E143_card_p9067; unfold a_p; omega
theorem BSD_ap_p9091 : a_p 9091 = (163 : ℤ) := by
  have h := BSD_E143_card_p9091; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9007: a_p=+143, 4p-a_p²=15579
theorem BSD_DegreeNonneg_p9007 : BSD_FrobeniusDegreeNonneg_OPEN 9007 := fun r => by
  have hap : (a_p 9007 : ℝ) = 143 := by exact_mod_cast BSD_ap_p9007
  have key : r ^ 2 - (a_p 9007 : ℝ) * r + ((9007 : ℕ) : ℝ) =
      (r - 143/2) ^ 2 + 15579/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (143 : ℝ)/2)]

-- p=9011: a_p=+96, 4p-a_p²=26828
theorem BSD_DegreeNonneg_p9011 : BSD_FrobeniusDegreeNonneg_OPEN 9011 := fun r => by
  have hap : (a_p 9011 : ℝ) = 96 := by exact_mod_cast BSD_ap_p9011
  have key : r ^ 2 - (a_p 9011 : ℝ) * r + ((9011 : ℕ) : ℝ) =
      (r - 96/2) ^ 2 + 26828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (96 : ℝ)/2)]

-- p=9013: a_p=+67, 4p-a_p²=31563
theorem BSD_DegreeNonneg_p9013 : BSD_FrobeniusDegreeNonneg_OPEN 9013 := fun r => by
  have hap : (a_p 9013 : ℝ) = 67 := by exact_mod_cast BSD_ap_p9013
  have key : r ^ 2 - (a_p 9013 : ℝ) * r + ((9013 : ℕ) : ℝ) =
      (r - 67/2) ^ 2 + 31563/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (67 : ℝ)/2)]

-- p=9029: a_p=+105, 4p-a_p²=25091
theorem BSD_DegreeNonneg_p9029 : BSD_FrobeniusDegreeNonneg_OPEN 9029 := fun r => by
  have hap : (a_p 9029 : ℝ) = 105 := by exact_mod_cast BSD_ap_p9029
  have key : r ^ 2 - (a_p 9029 : ℝ) * r + ((9029 : ℕ) : ℝ) =
      (r - 105/2) ^ 2 + 25091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (105 : ℝ)/2)]

-- p=9041: a_p=-12, 4p-a_p²=36020
theorem BSD_DegreeNonneg_p9041 : BSD_FrobeniusDegreeNonneg_OPEN 9041 := fun r => by
  have hap : (a_p 9041 : ℝ) = -12 := by exact_mod_cast BSD_ap_p9041
  have key : r ^ 2 - (a_p 9041 : ℝ) * r + ((9041 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 36020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

-- p=9043: a_p=-132, 4p-a_p²=18748
theorem BSD_DegreeNonneg_p9043 : BSD_FrobeniusDegreeNonneg_OPEN 9043 := fun r => by
  have hap : (a_p 9043 : ℝ) = -132 := by exact_mod_cast BSD_ap_p9043
  have key : r ^ 2 - (a_p 9043 : ℝ) * r + ((9043 : ℕ) : ℝ) =
      (r + 132/2) ^ 2 + 18748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (132 : ℝ)/2)]

-- p=9049: a_p=+44, 4p-a_p²=34260
theorem BSD_DegreeNonneg_p9049 : BSD_FrobeniusDegreeNonneg_OPEN 9049 := fun r => by
  have hap : (a_p 9049 : ℝ) = 44 := by exact_mod_cast BSD_ap_p9049
  have key : r ^ 2 - (a_p 9049 : ℝ) * r + ((9049 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 34260/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

-- p=9059: a_p=-54, 4p-a_p²=33320
theorem BSD_DegreeNonneg_p9059 : BSD_FrobeniusDegreeNonneg_OPEN 9059 := fun r => by
  have hap : (a_p 9059 : ℝ) = -54 := by exact_mod_cast BSD_ap_p9059
  have key : r ^ 2 - (a_p 9059 : ℝ) * r + ((9059 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 33320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

-- p=9067: a_p=-65, 4p-a_p²=32043
theorem BSD_DegreeNonneg_p9067 : BSD_FrobeniusDegreeNonneg_OPEN 9067 := fun r => by
  have hap : (a_p 9067 : ℝ) = -65 := by exact_mod_cast BSD_ap_p9067
  have key : r ^ 2 - (a_p 9067 : ℝ) * r + ((9067 : ℕ) : ℝ) =
      (r + 65/2) ^ 2 + 32043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (65 : ℝ)/2)]

-- p=9091: a_p=+163, 4p-a_p²=9795
theorem BSD_DegreeNonneg_p9091 : BSD_FrobeniusDegreeNonneg_OPEN 9091 := fun r => by
  have hap : (a_p 9091 : ℝ) = 163 := by exact_mod_cast BSD_ap_p9091
  have key : r ^ 2 - (a_p 9091 : ℝ) * r + ((9091 : ℕ) : ℝ) =
      (r - 163/2) ^ 2 + 9795/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (163 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9007 : BSD_Hasse_OPEN 9007 :=
  BSD_hasse_of_degree_nonneg 9007 BSD_DegreeNonneg_p9007
theorem BSD_Hasse_OPEN_p9011 : BSD_Hasse_OPEN 9011 :=
  BSD_hasse_of_degree_nonneg 9011 BSD_DegreeNonneg_p9011
theorem BSD_Hasse_OPEN_p9013 : BSD_Hasse_OPEN 9013 :=
  BSD_hasse_of_degree_nonneg 9013 BSD_DegreeNonneg_p9013
theorem BSD_Hasse_OPEN_p9029 : BSD_Hasse_OPEN 9029 :=
  BSD_hasse_of_degree_nonneg 9029 BSD_DegreeNonneg_p9029
theorem BSD_Hasse_OPEN_p9041 : BSD_Hasse_OPEN 9041 :=
  BSD_hasse_of_degree_nonneg 9041 BSD_DegreeNonneg_p9041
theorem BSD_Hasse_OPEN_p9043 : BSD_Hasse_OPEN 9043 :=
  BSD_hasse_of_degree_nonneg 9043 BSD_DegreeNonneg_p9043
theorem BSD_Hasse_OPEN_p9049 : BSD_Hasse_OPEN 9049 :=
  BSD_hasse_of_degree_nonneg 9049 BSD_DegreeNonneg_p9049
theorem BSD_Hasse_OPEN_p9059 : BSD_Hasse_OPEN 9059 :=
  BSD_hasse_of_degree_nonneg 9059 BSD_DegreeNonneg_p9059
theorem BSD_Hasse_OPEN_p9067 : BSD_Hasse_OPEN 9067 :=
  BSD_hasse_of_degree_nonneg 9067 BSD_DegreeNonneg_p9067
theorem BSD_Hasse_OPEN_p9091 : BSD_Hasse_OPEN 9091 :=
  BSD_hasse_of_degree_nonneg 9091 BSD_DegreeNonneg_p9091

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9007 : (a_p 9007 : ℝ) ^ 2 ≤ 4 * (9007 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9007
theorem BSD_HasseBound_Disc_p9011 : (a_p 9011 : ℝ) ^ 2 ≤ 4 * (9011 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9011
theorem BSD_HasseBound_Disc_p9013 : (a_p 9013 : ℝ) ^ 2 ≤ 4 * (9013 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9013
theorem BSD_HasseBound_Disc_p9029 : (a_p 9029 : ℝ) ^ 2 ≤ 4 * (9029 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9029
theorem BSD_HasseBound_Disc_p9041 : (a_p 9041 : ℝ) ^ 2 ≤ 4 * (9041 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9041
theorem BSD_HasseBound_Disc_p9043 : (a_p 9043 : ℝ) ^ 2 ≤ 4 * (9043 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9043
theorem BSD_HasseBound_Disc_p9049 : (a_p 9049 : ℝ) ^ 2 ≤ 4 * (9049 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9049
theorem BSD_HasseBound_Disc_p9059 : (a_p 9059 : ℝ) ^ 2 ≤ 4 * (9059 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9059
theorem BSD_HasseBound_Disc_p9067 : (a_p 9067 : ℝ) ^ 2 ≤ 4 * (9067 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9067
theorem BSD_HasseBound_Disc_p9091 : (a_p 9091 : ℝ) ^ 2 ≤ 4 * (9091 : ℝ) :=
  BSD_disc_from_deg_878 BSD_DegreeNonneg_p9091

end Towers.BSD