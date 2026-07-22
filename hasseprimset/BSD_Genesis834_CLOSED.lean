/-
================================================================
Towers / BSD / BSD_Genesis834_CLOSED  (genesis-834)

HasseBridge Tier C: Hasse bounds for primes
5081..5167 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5081: card=5100, a_p=-18, disc=-20000
  p=5087: card=5191, a_p=-103, disc=-9739
  p=5099: card=4988, a_p=+112, disc=-7852
  p=5101: card=5064, a_p=+38, disc=-18960
  p=5107: card=5176, a_p=-68, disc=-15804
  p=5113: card=5253, a_p=-139, disc=-1131
  p=5119: card=5153, a_p=-33, disc=-19387
  p=5147: card=5244, a_p=-96, disc=-11372
  p=5153: card=5175, a_p=-21, disc=-20171
  p=5167: card=5082, a_p=+86, disc=-13272

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_834 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i834_p5081 : Fact (5081 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5087 : Fact (5087 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5099 : Fact (5099 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5101 : Fact (5101 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5107 : Fact (5107 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5113 : Fact (5113 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5119 : Fact (5119 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5147 : Fact (5147 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5153 : Fact (5153 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5167 : Fact (5167 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5081 : (E143_Finset 5081).card = 5100 := by native_decide
theorem BSD_E143_card_p5087 : (E143_Finset 5087).card = 5191 := by native_decide
theorem BSD_E143_card_p5099 : (E143_Finset 5099).card = 4988 := by native_decide
theorem BSD_E143_card_p5101 : (E143_Finset 5101).card = 5064 := by native_decide
theorem BSD_E143_card_p5107 : (E143_Finset 5107).card = 5176 := by native_decide
theorem BSD_E143_card_p5113 : (E143_Finset 5113).card = 5253 := by native_decide
theorem BSD_E143_card_p5119 : (E143_Finset 5119).card = 5153 := by native_decide
theorem BSD_E143_card_p5147 : (E143_Finset 5147).card = 5244 := by native_decide
theorem BSD_E143_card_p5153 : (E143_Finset 5153).card = 5175 := by native_decide
theorem BSD_E143_card_p5167 : (E143_Finset 5167).card = 5082 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5081 : a_p 5081 = (-18 : ℤ) := by
  have h := BSD_E143_card_p5081; unfold a_p; omega
theorem BSD_ap_p5087 : a_p 5087 = (-103 : ℤ) := by
  have h := BSD_E143_card_p5087; unfold a_p; omega
theorem BSD_ap_p5099 : a_p 5099 = (112 : ℤ) := by
  have h := BSD_E143_card_p5099; unfold a_p; omega
theorem BSD_ap_p5101 : a_p 5101 = (38 : ℤ) := by
  have h := BSD_E143_card_p5101; unfold a_p; omega
theorem BSD_ap_p5107 : a_p 5107 = (-68 : ℤ) := by
  have h := BSD_E143_card_p5107; unfold a_p; omega
theorem BSD_ap_p5113 : a_p 5113 = (-139 : ℤ) := by
  have h := BSD_E143_card_p5113; unfold a_p; omega
theorem BSD_ap_p5119 : a_p 5119 = (-33 : ℤ) := by
  have h := BSD_E143_card_p5119; unfold a_p; omega
theorem BSD_ap_p5147 : a_p 5147 = (-96 : ℤ) := by
  have h := BSD_E143_card_p5147; unfold a_p; omega
theorem BSD_ap_p5153 : a_p 5153 = (-21 : ℤ) := by
  have h := BSD_E143_card_p5153; unfold a_p; omega
theorem BSD_ap_p5167 : a_p 5167 = (86 : ℤ) := by
  have h := BSD_E143_card_p5167; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5081: a_p=-18, 4p-a_p²=20000
theorem BSD_DegreeNonneg_p5081 : BSD_FrobeniusDegreeNonneg_OPEN 5081 := fun r => by
  have hap : (a_p 5081 : ℝ) = -18 := by exact_mod_cast BSD_ap_p5081
  have key : r ^ 2 - (a_p 5081 : ℝ) * r + ((5081 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 20000/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

-- p=5087: a_p=-103, 4p-a_p²=9739
theorem BSD_DegreeNonneg_p5087 : BSD_FrobeniusDegreeNonneg_OPEN 5087 := fun r => by
  have hap : (a_p 5087 : ℝ) = -103 := by exact_mod_cast BSD_ap_p5087
  have key : r ^ 2 - (a_p 5087 : ℝ) * r + ((5087 : ℕ) : ℝ) =
      (r + 103/2) ^ 2 + 9739/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (103 : ℝ)/2)]

-- p=5099: a_p=+112, 4p-a_p²=7852
theorem BSD_DegreeNonneg_p5099 : BSD_FrobeniusDegreeNonneg_OPEN 5099 := fun r => by
  have hap : (a_p 5099 : ℝ) = 112 := by exact_mod_cast BSD_ap_p5099
  have key : r ^ 2 - (a_p 5099 : ℝ) * r + ((5099 : ℕ) : ℝ) =
      (r - 112/2) ^ 2 + 7852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (112 : ℝ)/2)]

-- p=5101: a_p=+38, 4p-a_p²=18960
theorem BSD_DegreeNonneg_p5101 : BSD_FrobeniusDegreeNonneg_OPEN 5101 := fun r => by
  have hap : (a_p 5101 : ℝ) = 38 := by exact_mod_cast BSD_ap_p5101
  have key : r ^ 2 - (a_p 5101 : ℝ) * r + ((5101 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 18960/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

-- p=5107: a_p=-68, 4p-a_p²=15804
theorem BSD_DegreeNonneg_p5107 : BSD_FrobeniusDegreeNonneg_OPEN 5107 := fun r => by
  have hap : (a_p 5107 : ℝ) = -68 := by exact_mod_cast BSD_ap_p5107
  have key : r ^ 2 - (a_p 5107 : ℝ) * r + ((5107 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 15804/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

-- p=5113: a_p=-139, 4p-a_p²=1131
theorem BSD_DegreeNonneg_p5113 : BSD_FrobeniusDegreeNonneg_OPEN 5113 := fun r => by
  have hap : (a_p 5113 : ℝ) = -139 := by exact_mod_cast BSD_ap_p5113
  have key : r ^ 2 - (a_p 5113 : ℝ) * r + ((5113 : ℕ) : ℝ) =
      (r + 139/2) ^ 2 + 1131/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (139 : ℝ)/2)]

-- p=5119: a_p=-33, 4p-a_p²=19387
theorem BSD_DegreeNonneg_p5119 : BSD_FrobeniusDegreeNonneg_OPEN 5119 := fun r => by
  have hap : (a_p 5119 : ℝ) = -33 := by exact_mod_cast BSD_ap_p5119
  have key : r ^ 2 - (a_p 5119 : ℝ) * r + ((5119 : ℕ) : ℝ) =
      (r + 33/2) ^ 2 + 19387/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (33 : ℝ)/2)]

-- p=5147: a_p=-96, 4p-a_p²=11372
theorem BSD_DegreeNonneg_p5147 : BSD_FrobeniusDegreeNonneg_OPEN 5147 := fun r => by
  have hap : (a_p 5147 : ℝ) = -96 := by exact_mod_cast BSD_ap_p5147
  have key : r ^ 2 - (a_p 5147 : ℝ) * r + ((5147 : ℕ) : ℝ) =
      (r + 96/2) ^ 2 + 11372/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (96 : ℝ)/2)]

-- p=5153: a_p=-21, 4p-a_p²=20171
theorem BSD_DegreeNonneg_p5153 : BSD_FrobeniusDegreeNonneg_OPEN 5153 := fun r => by
  have hap : (a_p 5153 : ℝ) = -21 := by exact_mod_cast BSD_ap_p5153
  have key : r ^ 2 - (a_p 5153 : ℝ) * r + ((5153 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 20171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

-- p=5167: a_p=+86, 4p-a_p²=13272
theorem BSD_DegreeNonneg_p5167 : BSD_FrobeniusDegreeNonneg_OPEN 5167 := fun r => by
  have hap : (a_p 5167 : ℝ) = 86 := by exact_mod_cast BSD_ap_p5167
  have key : r ^ 2 - (a_p 5167 : ℝ) * r + ((5167 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 13272/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5081 : BSD_Hasse_OPEN 5081 :=
  BSD_hasse_of_degree_nonneg 5081 BSD_DegreeNonneg_p5081
theorem BSD_Hasse_OPEN_p5087 : BSD_Hasse_OPEN 5087 :=
  BSD_hasse_of_degree_nonneg 5087 BSD_DegreeNonneg_p5087
theorem BSD_Hasse_OPEN_p5099 : BSD_Hasse_OPEN 5099 :=
  BSD_hasse_of_degree_nonneg 5099 BSD_DegreeNonneg_p5099
theorem BSD_Hasse_OPEN_p5101 : BSD_Hasse_OPEN 5101 :=
  BSD_hasse_of_degree_nonneg 5101 BSD_DegreeNonneg_p5101
theorem BSD_Hasse_OPEN_p5107 : BSD_Hasse_OPEN 5107 :=
  BSD_hasse_of_degree_nonneg 5107 BSD_DegreeNonneg_p5107
theorem BSD_Hasse_OPEN_p5113 : BSD_Hasse_OPEN 5113 :=
  BSD_hasse_of_degree_nonneg 5113 BSD_DegreeNonneg_p5113
theorem BSD_Hasse_OPEN_p5119 : BSD_Hasse_OPEN 5119 :=
  BSD_hasse_of_degree_nonneg 5119 BSD_DegreeNonneg_p5119
theorem BSD_Hasse_OPEN_p5147 : BSD_Hasse_OPEN 5147 :=
  BSD_hasse_of_degree_nonneg 5147 BSD_DegreeNonneg_p5147
theorem BSD_Hasse_OPEN_p5153 : BSD_Hasse_OPEN 5153 :=
  BSD_hasse_of_degree_nonneg 5153 BSD_DegreeNonneg_p5153
theorem BSD_Hasse_OPEN_p5167 : BSD_Hasse_OPEN 5167 :=
  BSD_hasse_of_degree_nonneg 5167 BSD_DegreeNonneg_p5167

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5081 : (a_p 5081 : ℝ) ^ 2 ≤ 4 * (5081 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5081
theorem BSD_HasseBound_Disc_p5087 : (a_p 5087 : ℝ) ^ 2 ≤ 4 * (5087 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5087
theorem BSD_HasseBound_Disc_p5099 : (a_p 5099 : ℝ) ^ 2 ≤ 4 * (5099 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5099
theorem BSD_HasseBound_Disc_p5101 : (a_p 5101 : ℝ) ^ 2 ≤ 4 * (5101 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5101
theorem BSD_HasseBound_Disc_p5107 : (a_p 5107 : ℝ) ^ 2 ≤ 4 * (5107 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5107
theorem BSD_HasseBound_Disc_p5113 : (a_p 5113 : ℝ) ^ 2 ≤ 4 * (5113 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5113
theorem BSD_HasseBound_Disc_p5119 : (a_p 5119 : ℝ) ^ 2 ≤ 4 * (5119 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5119
theorem BSD_HasseBound_Disc_p5147 : (a_p 5147 : ℝ) ^ 2 ≤ 4 * (5147 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5147
theorem BSD_HasseBound_Disc_p5153 : (a_p 5153 : ℝ) ^ 2 ≤ 4 * (5153 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5153
theorem BSD_HasseBound_Disc_p5167 : (a_p 5167 : ℝ) ^ 2 ≤ 4 * (5167 : ℝ) :=
  BSD_disc_from_deg_834 BSD_DegreeNonneg_p5167

end Towers.BSD