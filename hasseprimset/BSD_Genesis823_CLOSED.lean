/-
================================================================
Towers / BSD / BSD_Genesis823_CLOSED  (genesis-823)

HasseBridge Tier C: Hasse bounds for primes
4133..4219 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4133: card=4032, a_p=+102, disc=-6128
  p=4139: card=4180, a_p=-40, disc=-14956
  p=4153: card=4196, a_p=-42, disc=-14848
  p=4157: card=4100, a_p=+58, disc=-13264
  p=4159: card=4235, a_p=-75, disc=-11011
  p=4177: card=4076, a_p=+102, disc=-6304
  p=4201: card=4224, a_p=-22, disc=-16320
  p=4211: card=4295, a_p=-83, disc=-9955
  p=4217: card=4323, a_p=-105, disc=-5843
  p=4219: card=4238, a_p=-18, disc=-16552

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_823 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i823_p4133 : Fact (4133 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4139 : Fact (4139 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4153 : Fact (4153 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4157 : Fact (4157 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4159 : Fact (4159 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4177 : Fact (4177 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4201 : Fact (4201 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4211 : Fact (4211 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4217 : Fact (4217 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4219 : Fact (4219 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4133 : (E143_Finset 4133).card = 4032 := by native_decide
theorem BSD_E143_card_p4139 : (E143_Finset 4139).card = 4180 := by native_decide
theorem BSD_E143_card_p4153 : (E143_Finset 4153).card = 4196 := by native_decide
theorem BSD_E143_card_p4157 : (E143_Finset 4157).card = 4100 := by native_decide
theorem BSD_E143_card_p4159 : (E143_Finset 4159).card = 4235 := by native_decide
theorem BSD_E143_card_p4177 : (E143_Finset 4177).card = 4076 := by native_decide
theorem BSD_E143_card_p4201 : (E143_Finset 4201).card = 4224 := by native_decide
theorem BSD_E143_card_p4211 : (E143_Finset 4211).card = 4295 := by native_decide
theorem BSD_E143_card_p4217 : (E143_Finset 4217).card = 4323 := by native_decide
theorem BSD_E143_card_p4219 : (E143_Finset 4219).card = 4238 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4133 : a_p 4133 = (102 : ℤ) := by
  have h := BSD_E143_card_p4133; unfold a_p; omega
theorem BSD_ap_p4139 : a_p 4139 = (-40 : ℤ) := by
  have h := BSD_E143_card_p4139; unfold a_p; omega
theorem BSD_ap_p4153 : a_p 4153 = (-42 : ℤ) := by
  have h := BSD_E143_card_p4153; unfold a_p; omega
theorem BSD_ap_p4157 : a_p 4157 = (58 : ℤ) := by
  have h := BSD_E143_card_p4157; unfold a_p; omega
theorem BSD_ap_p4159 : a_p 4159 = (-75 : ℤ) := by
  have h := BSD_E143_card_p4159; unfold a_p; omega
theorem BSD_ap_p4177 : a_p 4177 = (102 : ℤ) := by
  have h := BSD_E143_card_p4177; unfold a_p; omega
theorem BSD_ap_p4201 : a_p 4201 = (-22 : ℤ) := by
  have h := BSD_E143_card_p4201; unfold a_p; omega
theorem BSD_ap_p4211 : a_p 4211 = (-83 : ℤ) := by
  have h := BSD_E143_card_p4211; unfold a_p; omega
theorem BSD_ap_p4217 : a_p 4217 = (-105 : ℤ) := by
  have h := BSD_E143_card_p4217; unfold a_p; omega
theorem BSD_ap_p4219 : a_p 4219 = (-18 : ℤ) := by
  have h := BSD_E143_card_p4219; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4133: a_p=+102, 4p-a_p²=6128
theorem BSD_DegreeNonneg_p4133 : BSD_FrobeniusDegreeNonneg_OPEN 4133 := fun r => by
  have hap : (a_p 4133 : ℝ) = 102 := by exact_mod_cast BSD_ap_p4133
  have key : r ^ 2 - (a_p 4133 : ℝ) * r + ((4133 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 6128/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

-- p=4139: a_p=-40, 4p-a_p²=14956
theorem BSD_DegreeNonneg_p4139 : BSD_FrobeniusDegreeNonneg_OPEN 4139 := fun r => by
  have hap : (a_p 4139 : ℝ) = -40 := by exact_mod_cast BSD_ap_p4139
  have key : r ^ 2 - (a_p 4139 : ℝ) * r + ((4139 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 14956/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

-- p=4153: a_p=-42, 4p-a_p²=14848
theorem BSD_DegreeNonneg_p4153 : BSD_FrobeniusDegreeNonneg_OPEN 4153 := fun r => by
  have hap : (a_p 4153 : ℝ) = -42 := by exact_mod_cast BSD_ap_p4153
  have key : r ^ 2 - (a_p 4153 : ℝ) * r + ((4153 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 14848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

-- p=4157: a_p=+58, 4p-a_p²=13264
theorem BSD_DegreeNonneg_p4157 : BSD_FrobeniusDegreeNonneg_OPEN 4157 := fun r => by
  have hap : (a_p 4157 : ℝ) = 58 := by exact_mod_cast BSD_ap_p4157
  have key : r ^ 2 - (a_p 4157 : ℝ) * r + ((4157 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 13264/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

-- p=4159: a_p=-75, 4p-a_p²=11011
theorem BSD_DegreeNonneg_p4159 : BSD_FrobeniusDegreeNonneg_OPEN 4159 := fun r => by
  have hap : (a_p 4159 : ℝ) = -75 := by exact_mod_cast BSD_ap_p4159
  have key : r ^ 2 - (a_p 4159 : ℝ) * r + ((4159 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 11011/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

-- p=4177: a_p=+102, 4p-a_p²=6304
theorem BSD_DegreeNonneg_p4177 : BSD_FrobeniusDegreeNonneg_OPEN 4177 := fun r => by
  have hap : (a_p 4177 : ℝ) = 102 := by exact_mod_cast BSD_ap_p4177
  have key : r ^ 2 - (a_p 4177 : ℝ) * r + ((4177 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 6304/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

-- p=4201: a_p=-22, 4p-a_p²=16320
theorem BSD_DegreeNonneg_p4201 : BSD_FrobeniusDegreeNonneg_OPEN 4201 := fun r => by
  have hap : (a_p 4201 : ℝ) = -22 := by exact_mod_cast BSD_ap_p4201
  have key : r ^ 2 - (a_p 4201 : ℝ) * r + ((4201 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 16320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=4211: a_p=-83, 4p-a_p²=9955
theorem BSD_DegreeNonneg_p4211 : BSD_FrobeniusDegreeNonneg_OPEN 4211 := fun r => by
  have hap : (a_p 4211 : ℝ) = -83 := by exact_mod_cast BSD_ap_p4211
  have key : r ^ 2 - (a_p 4211 : ℝ) * r + ((4211 : ℕ) : ℝ) =
      (r + 83/2) ^ 2 + 9955/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (83 : ℝ)/2)]

-- p=4217: a_p=-105, 4p-a_p²=5843
theorem BSD_DegreeNonneg_p4217 : BSD_FrobeniusDegreeNonneg_OPEN 4217 := fun r => by
  have hap : (a_p 4217 : ℝ) = -105 := by exact_mod_cast BSD_ap_p4217
  have key : r ^ 2 - (a_p 4217 : ℝ) * r + ((4217 : ℕ) : ℝ) =
      (r + 105/2) ^ 2 + 5843/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (105 : ℝ)/2)]

-- p=4219: a_p=-18, 4p-a_p²=16552
theorem BSD_DegreeNonneg_p4219 : BSD_FrobeniusDegreeNonneg_OPEN 4219 := fun r => by
  have hap : (a_p 4219 : ℝ) = -18 := by exact_mod_cast BSD_ap_p4219
  have key : r ^ 2 - (a_p 4219 : ℝ) * r + ((4219 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 16552/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4133 : BSD_Hasse_OPEN 4133 :=
  BSD_hasse_of_degree_nonneg 4133 BSD_DegreeNonneg_p4133
theorem BSD_Hasse_OPEN_p4139 : BSD_Hasse_OPEN 4139 :=
  BSD_hasse_of_degree_nonneg 4139 BSD_DegreeNonneg_p4139
theorem BSD_Hasse_OPEN_p4153 : BSD_Hasse_OPEN 4153 :=
  BSD_hasse_of_degree_nonneg 4153 BSD_DegreeNonneg_p4153
theorem BSD_Hasse_OPEN_p4157 : BSD_Hasse_OPEN 4157 :=
  BSD_hasse_of_degree_nonneg 4157 BSD_DegreeNonneg_p4157
theorem BSD_Hasse_OPEN_p4159 : BSD_Hasse_OPEN 4159 :=
  BSD_hasse_of_degree_nonneg 4159 BSD_DegreeNonneg_p4159
theorem BSD_Hasse_OPEN_p4177 : BSD_Hasse_OPEN 4177 :=
  BSD_hasse_of_degree_nonneg 4177 BSD_DegreeNonneg_p4177
theorem BSD_Hasse_OPEN_p4201 : BSD_Hasse_OPEN 4201 :=
  BSD_hasse_of_degree_nonneg 4201 BSD_DegreeNonneg_p4201
theorem BSD_Hasse_OPEN_p4211 : BSD_Hasse_OPEN 4211 :=
  BSD_hasse_of_degree_nonneg 4211 BSD_DegreeNonneg_p4211
theorem BSD_Hasse_OPEN_p4217 : BSD_Hasse_OPEN 4217 :=
  BSD_hasse_of_degree_nonneg 4217 BSD_DegreeNonneg_p4217
theorem BSD_Hasse_OPEN_p4219 : BSD_Hasse_OPEN 4219 :=
  BSD_hasse_of_degree_nonneg 4219 BSD_DegreeNonneg_p4219

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4133 : (a_p 4133 : ℝ) ^ 2 ≤ 4 * (4133 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4133
theorem BSD_HasseBound_Disc_p4139 : (a_p 4139 : ℝ) ^ 2 ≤ 4 * (4139 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4139
theorem BSD_HasseBound_Disc_p4153 : (a_p 4153 : ℝ) ^ 2 ≤ 4 * (4153 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4153
theorem BSD_HasseBound_Disc_p4157 : (a_p 4157 : ℝ) ^ 2 ≤ 4 * (4157 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4157
theorem BSD_HasseBound_Disc_p4159 : (a_p 4159 : ℝ) ^ 2 ≤ 4 * (4159 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4159
theorem BSD_HasseBound_Disc_p4177 : (a_p 4177 : ℝ) ^ 2 ≤ 4 * (4177 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4177
theorem BSD_HasseBound_Disc_p4201 : (a_p 4201 : ℝ) ^ 2 ≤ 4 * (4201 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4201
theorem BSD_HasseBound_Disc_p4211 : (a_p 4211 : ℝ) ^ 2 ≤ 4 * (4211 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4211
theorem BSD_HasseBound_Disc_p4217 : (a_p 4217 : ℝ) ^ 2 ≤ 4 * (4217 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4217
theorem BSD_HasseBound_Disc_p4219 : (a_p 4219 : ℝ) ^ 2 ≤ 4 * (4219 : ℝ) :=
  BSD_disc_from_deg_823 BSD_DegreeNonneg_p4219

end Towers.BSD