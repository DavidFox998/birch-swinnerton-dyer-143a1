/-
================================================================
Towers / BSD / BSD_Genesis835_CLOSED  (genesis-835)

HasseBridge Tier C: Hasse bounds for primes
5171..5261 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5171: card=5075, a_p=+97, disc=-11275
  p=5179: card=5164, a_p=+16, disc=-20460
  p=5189: card=5226, a_p=-36, disc=-19460
  p=5197: card=5091, a_p=+107, disc=-9339
  p=5209: card=5204, a_p=+6, disc=-20800
  p=5227: card=5284, a_p=-56, disc=-17772
  p=5231: card=5242, a_p=-10, disc=-20824
  p=5233: card=5182, a_p=+52, disc=-18228
  p=5237: card=5173, a_p=+65, disc=-16723
  p=5261: card=5267, a_p=-5, disc=-21019

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_835 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i835_p5171 : Fact (5171 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5179 : Fact (5179 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5189 : Fact (5189 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5197 : Fact (5197 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5209 : Fact (5209 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5227 : Fact (5227 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5231 : Fact (5231 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5233 : Fact (5233 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5237 : Fact (5237 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5261 : Fact (5261 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5171 : (E143_Finset 5171).card = 5075 := by native_decide
theorem BSD_E143_card_p5179 : (E143_Finset 5179).card = 5164 := by native_decide
theorem BSD_E143_card_p5189 : (E143_Finset 5189).card = 5226 := by native_decide
theorem BSD_E143_card_p5197 : (E143_Finset 5197).card = 5091 := by native_decide
theorem BSD_E143_card_p5209 : (E143_Finset 5209).card = 5204 := by native_decide
theorem BSD_E143_card_p5227 : (E143_Finset 5227).card = 5284 := by native_decide
theorem BSD_E143_card_p5231 : (E143_Finset 5231).card = 5242 := by native_decide
theorem BSD_E143_card_p5233 : (E143_Finset 5233).card = 5182 := by native_decide
theorem BSD_E143_card_p5237 : (E143_Finset 5237).card = 5173 := by native_decide
theorem BSD_E143_card_p5261 : (E143_Finset 5261).card = 5267 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5171 : a_p 5171 = (97 : ℤ) := by
  have h := BSD_E143_card_p5171; unfold a_p; omega
theorem BSD_ap_p5179 : a_p 5179 = (16 : ℤ) := by
  have h := BSD_E143_card_p5179; unfold a_p; omega
theorem BSD_ap_p5189 : a_p 5189 = (-36 : ℤ) := by
  have h := BSD_E143_card_p5189; unfold a_p; omega
theorem BSD_ap_p5197 : a_p 5197 = (107 : ℤ) := by
  have h := BSD_E143_card_p5197; unfold a_p; omega
theorem BSD_ap_p5209 : a_p 5209 = (6 : ℤ) := by
  have h := BSD_E143_card_p5209; unfold a_p; omega
theorem BSD_ap_p5227 : a_p 5227 = (-56 : ℤ) := by
  have h := BSD_E143_card_p5227; unfold a_p; omega
theorem BSD_ap_p5231 : a_p 5231 = (-10 : ℤ) := by
  have h := BSD_E143_card_p5231; unfold a_p; omega
theorem BSD_ap_p5233 : a_p 5233 = (52 : ℤ) := by
  have h := BSD_E143_card_p5233; unfold a_p; omega
theorem BSD_ap_p5237 : a_p 5237 = (65 : ℤ) := by
  have h := BSD_E143_card_p5237; unfold a_p; omega
theorem BSD_ap_p5261 : a_p 5261 = (-5 : ℤ) := by
  have h := BSD_E143_card_p5261; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5171: a_p=+97, 4p-a_p²=11275
theorem BSD_DegreeNonneg_p5171 : BSD_FrobeniusDegreeNonneg_OPEN 5171 := fun r => by
  have hap : (a_p 5171 : ℝ) = 97 := by exact_mod_cast BSD_ap_p5171
  have key : r ^ 2 - (a_p 5171 : ℝ) * r + ((5171 : ℕ) : ℝ) =
      (r - 97/2) ^ 2 + 11275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (97 : ℝ)/2)]

-- p=5179: a_p=+16, 4p-a_p²=20460
theorem BSD_DegreeNonneg_p5179 : BSD_FrobeniusDegreeNonneg_OPEN 5179 := fun r => by
  have hap : (a_p 5179 : ℝ) = 16 := by exact_mod_cast BSD_ap_p5179
  have key : r ^ 2 - (a_p 5179 : ℝ) * r + ((5179 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 20460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

-- p=5189: a_p=-36, 4p-a_p²=19460
theorem BSD_DegreeNonneg_p5189 : BSD_FrobeniusDegreeNonneg_OPEN 5189 := fun r => by
  have hap : (a_p 5189 : ℝ) = -36 := by exact_mod_cast BSD_ap_p5189
  have key : r ^ 2 - (a_p 5189 : ℝ) * r + ((5189 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 19460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

-- p=5197: a_p=+107, 4p-a_p²=9339
theorem BSD_DegreeNonneg_p5197 : BSD_FrobeniusDegreeNonneg_OPEN 5197 := fun r => by
  have hap : (a_p 5197 : ℝ) = 107 := by exact_mod_cast BSD_ap_p5197
  have key : r ^ 2 - (a_p 5197 : ℝ) * r + ((5197 : ℕ) : ℝ) =
      (r - 107/2) ^ 2 + 9339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (107 : ℝ)/2)]

-- p=5209: a_p=+6, 4p-a_p²=20800
theorem BSD_DegreeNonneg_p5209 : BSD_FrobeniusDegreeNonneg_OPEN 5209 := fun r => by
  have hap : (a_p 5209 : ℝ) = 6 := by exact_mod_cast BSD_ap_p5209
  have key : r ^ 2 - (a_p 5209 : ℝ) * r + ((5209 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 20800/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

-- p=5227: a_p=-56, 4p-a_p²=17772
theorem BSD_DegreeNonneg_p5227 : BSD_FrobeniusDegreeNonneg_OPEN 5227 := fun r => by
  have hap : (a_p 5227 : ℝ) = -56 := by exact_mod_cast BSD_ap_p5227
  have key : r ^ 2 - (a_p 5227 : ℝ) * r + ((5227 : ℕ) : ℝ) =
      (r + 56/2) ^ 2 + 17772/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (56 : ℝ)/2)]

-- p=5231: a_p=-10, 4p-a_p²=20824
theorem BSD_DegreeNonneg_p5231 : BSD_FrobeniusDegreeNonneg_OPEN 5231 := fun r => by
  have hap : (a_p 5231 : ℝ) = -10 := by exact_mod_cast BSD_ap_p5231
  have key : r ^ 2 - (a_p 5231 : ℝ) * r + ((5231 : ℕ) : ℝ) =
      (r + 10/2) ^ 2 + 20824/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (10 : ℝ)/2)]

-- p=5233: a_p=+52, 4p-a_p²=18228
theorem BSD_DegreeNonneg_p5233 : BSD_FrobeniusDegreeNonneg_OPEN 5233 := fun r => by
  have hap : (a_p 5233 : ℝ) = 52 := by exact_mod_cast BSD_ap_p5233
  have key : r ^ 2 - (a_p 5233 : ℝ) * r + ((5233 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 18228/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

-- p=5237: a_p=+65, 4p-a_p²=16723
theorem BSD_DegreeNonneg_p5237 : BSD_FrobeniusDegreeNonneg_OPEN 5237 := fun r => by
  have hap : (a_p 5237 : ℝ) = 65 := by exact_mod_cast BSD_ap_p5237
  have key : r ^ 2 - (a_p 5237 : ℝ) * r + ((5237 : ℕ) : ℝ) =
      (r - 65/2) ^ 2 + 16723/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (65 : ℝ)/2)]

-- p=5261: a_p=-5, 4p-a_p²=21019
theorem BSD_DegreeNonneg_p5261 : BSD_FrobeniusDegreeNonneg_OPEN 5261 := fun r => by
  have hap : (a_p 5261 : ℝ) = -5 := by exact_mod_cast BSD_ap_p5261
  have key : r ^ 2 - (a_p 5261 : ℝ) * r + ((5261 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 21019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5171 : BSD_Hasse_OPEN 5171 :=
  BSD_hasse_of_degree_nonneg 5171 BSD_DegreeNonneg_p5171
theorem BSD_Hasse_OPEN_p5179 : BSD_Hasse_OPEN 5179 :=
  BSD_hasse_of_degree_nonneg 5179 BSD_DegreeNonneg_p5179
theorem BSD_Hasse_OPEN_p5189 : BSD_Hasse_OPEN 5189 :=
  BSD_hasse_of_degree_nonneg 5189 BSD_DegreeNonneg_p5189
theorem BSD_Hasse_OPEN_p5197 : BSD_Hasse_OPEN 5197 :=
  BSD_hasse_of_degree_nonneg 5197 BSD_DegreeNonneg_p5197
theorem BSD_Hasse_OPEN_p5209 : BSD_Hasse_OPEN 5209 :=
  BSD_hasse_of_degree_nonneg 5209 BSD_DegreeNonneg_p5209
theorem BSD_Hasse_OPEN_p5227 : BSD_Hasse_OPEN 5227 :=
  BSD_hasse_of_degree_nonneg 5227 BSD_DegreeNonneg_p5227
theorem BSD_Hasse_OPEN_p5231 : BSD_Hasse_OPEN 5231 :=
  BSD_hasse_of_degree_nonneg 5231 BSD_DegreeNonneg_p5231
theorem BSD_Hasse_OPEN_p5233 : BSD_Hasse_OPEN 5233 :=
  BSD_hasse_of_degree_nonneg 5233 BSD_DegreeNonneg_p5233
theorem BSD_Hasse_OPEN_p5237 : BSD_Hasse_OPEN 5237 :=
  BSD_hasse_of_degree_nonneg 5237 BSD_DegreeNonneg_p5237
theorem BSD_Hasse_OPEN_p5261 : BSD_Hasse_OPEN 5261 :=
  BSD_hasse_of_degree_nonneg 5261 BSD_DegreeNonneg_p5261

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5171 : (a_p 5171 : ℝ) ^ 2 ≤ 4 * (5171 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5171
theorem BSD_HasseBound_Disc_p5179 : (a_p 5179 : ℝ) ^ 2 ≤ 4 * (5179 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5179
theorem BSD_HasseBound_Disc_p5189 : (a_p 5189 : ℝ) ^ 2 ≤ 4 * (5189 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5189
theorem BSD_HasseBound_Disc_p5197 : (a_p 5197 : ℝ) ^ 2 ≤ 4 * (5197 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5197
theorem BSD_HasseBound_Disc_p5209 : (a_p 5209 : ℝ) ^ 2 ≤ 4 * (5209 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5209
theorem BSD_HasseBound_Disc_p5227 : (a_p 5227 : ℝ) ^ 2 ≤ 4 * (5227 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5227
theorem BSD_HasseBound_Disc_p5231 : (a_p 5231 : ℝ) ^ 2 ≤ 4 * (5231 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5231
theorem BSD_HasseBound_Disc_p5233 : (a_p 5233 : ℝ) ^ 2 ≤ 4 * (5233 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5233
theorem BSD_HasseBound_Disc_p5237 : (a_p 5237 : ℝ) ^ 2 ≤ 4 * (5237 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5237
theorem BSD_HasseBound_Disc_p5261 : (a_p 5261 : ℝ) ^ 2 ≤ 4 * (5261 : ℝ) :=
  BSD_disc_from_deg_835 BSD_DegreeNonneg_p5261

end Towers.BSD