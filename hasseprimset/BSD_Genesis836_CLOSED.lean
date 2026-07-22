/-
================================================================
Towers / BSD / BSD_Genesis836_CLOSED  (genesis-836)

HasseBridge Tier C: Hasse bounds for primes
5273..5351 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5273: card=5409, a_p=-135, disc=-2867
  p=5279: card=5344, a_p=-64, disc=-17020
  p=5281: card=5265, a_p=+17, disc=-20835
  p=5297: card=5430, a_p=-132, disc=-3764
  p=5303: card=5241, a_p=+63, disc=-17243
  p=5309: card=5274, a_p=+36, disc=-19940
  p=5323: card=5394, a_p=-70, disc=-16392
  p=5333: card=5220, a_p=+114, disc=-8336
  p=5347: card=5221, a_p=+127, disc=-5259
  p=5351: card=5357, a_p=-5, disc=-21379

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_836 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i836_p5273 : Fact (5273 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5279 : Fact (5279 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5281 : Fact (5281 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5297 : Fact (5297 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5303 : Fact (5303 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5309 : Fact (5309 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5323 : Fact (5323 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5333 : Fact (5333 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5347 : Fact (5347 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5351 : Fact (5351 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5273 : (E143_Finset 5273).card = 5409 := by native_decide
theorem BSD_E143_card_p5279 : (E143_Finset 5279).card = 5344 := by native_decide
theorem BSD_E143_card_p5281 : (E143_Finset 5281).card = 5265 := by native_decide
theorem BSD_E143_card_p5297 : (E143_Finset 5297).card = 5430 := by native_decide
theorem BSD_E143_card_p5303 : (E143_Finset 5303).card = 5241 := by native_decide
theorem BSD_E143_card_p5309 : (E143_Finset 5309).card = 5274 := by native_decide
theorem BSD_E143_card_p5323 : (E143_Finset 5323).card = 5394 := by native_decide
theorem BSD_E143_card_p5333 : (E143_Finset 5333).card = 5220 := by native_decide
theorem BSD_E143_card_p5347 : (E143_Finset 5347).card = 5221 := by native_decide
theorem BSD_E143_card_p5351 : (E143_Finset 5351).card = 5357 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5273 : a_p 5273 = (-135 : ℤ) := by
  have h := BSD_E143_card_p5273; unfold a_p; omega
theorem BSD_ap_p5279 : a_p 5279 = (-64 : ℤ) := by
  have h := BSD_E143_card_p5279; unfold a_p; omega
theorem BSD_ap_p5281 : a_p 5281 = (17 : ℤ) := by
  have h := BSD_E143_card_p5281; unfold a_p; omega
theorem BSD_ap_p5297 : a_p 5297 = (-132 : ℤ) := by
  have h := BSD_E143_card_p5297; unfold a_p; omega
theorem BSD_ap_p5303 : a_p 5303 = (63 : ℤ) := by
  have h := BSD_E143_card_p5303; unfold a_p; omega
theorem BSD_ap_p5309 : a_p 5309 = (36 : ℤ) := by
  have h := BSD_E143_card_p5309; unfold a_p; omega
theorem BSD_ap_p5323 : a_p 5323 = (-70 : ℤ) := by
  have h := BSD_E143_card_p5323; unfold a_p; omega
theorem BSD_ap_p5333 : a_p 5333 = (114 : ℤ) := by
  have h := BSD_E143_card_p5333; unfold a_p; omega
theorem BSD_ap_p5347 : a_p 5347 = (127 : ℤ) := by
  have h := BSD_E143_card_p5347; unfold a_p; omega
theorem BSD_ap_p5351 : a_p 5351 = (-5 : ℤ) := by
  have h := BSD_E143_card_p5351; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5273: a_p=-135, 4p-a_p²=2867
theorem BSD_DegreeNonneg_p5273 : BSD_FrobeniusDegreeNonneg_OPEN 5273 := fun r => by
  have hap : (a_p 5273 : ℝ) = -135 := by exact_mod_cast BSD_ap_p5273
  have key : r ^ 2 - (a_p 5273 : ℝ) * r + ((5273 : ℕ) : ℝ) =
      (r + 135/2) ^ 2 + 2867/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (135 : ℝ)/2)]

-- p=5279: a_p=-64, 4p-a_p²=17020
theorem BSD_DegreeNonneg_p5279 : BSD_FrobeniusDegreeNonneg_OPEN 5279 := fun r => by
  have hap : (a_p 5279 : ℝ) = -64 := by exact_mod_cast BSD_ap_p5279
  have key : r ^ 2 - (a_p 5279 : ℝ) * r + ((5279 : ℕ) : ℝ) =
      (r + 64/2) ^ 2 + 17020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (64 : ℝ)/2)]

-- p=5281: a_p=+17, 4p-a_p²=20835
theorem BSD_DegreeNonneg_p5281 : BSD_FrobeniusDegreeNonneg_OPEN 5281 := fun r => by
  have hap : (a_p 5281 : ℝ) = 17 := by exact_mod_cast BSD_ap_p5281
  have key : r ^ 2 - (a_p 5281 : ℝ) * r + ((5281 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 20835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

-- p=5297: a_p=-132, 4p-a_p²=3764
theorem BSD_DegreeNonneg_p5297 : BSD_FrobeniusDegreeNonneg_OPEN 5297 := fun r => by
  have hap : (a_p 5297 : ℝ) = -132 := by exact_mod_cast BSD_ap_p5297
  have key : r ^ 2 - (a_p 5297 : ℝ) * r + ((5297 : ℕ) : ℝ) =
      (r + 132/2) ^ 2 + 3764/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (132 : ℝ)/2)]

-- p=5303: a_p=+63, 4p-a_p²=17243
theorem BSD_DegreeNonneg_p5303 : BSD_FrobeniusDegreeNonneg_OPEN 5303 := fun r => by
  have hap : (a_p 5303 : ℝ) = 63 := by exact_mod_cast BSD_ap_p5303
  have key : r ^ 2 - (a_p 5303 : ℝ) * r + ((5303 : ℕ) : ℝ) =
      (r - 63/2) ^ 2 + 17243/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (63 : ℝ)/2)]

-- p=5309: a_p=+36, 4p-a_p²=19940
theorem BSD_DegreeNonneg_p5309 : BSD_FrobeniusDegreeNonneg_OPEN 5309 := fun r => by
  have hap : (a_p 5309 : ℝ) = 36 := by exact_mod_cast BSD_ap_p5309
  have key : r ^ 2 - (a_p 5309 : ℝ) * r + ((5309 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 19940/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

-- p=5323: a_p=-70, 4p-a_p²=16392
theorem BSD_DegreeNonneg_p5323 : BSD_FrobeniusDegreeNonneg_OPEN 5323 := fun r => by
  have hap : (a_p 5323 : ℝ) = -70 := by exact_mod_cast BSD_ap_p5323
  have key : r ^ 2 - (a_p 5323 : ℝ) * r + ((5323 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 16392/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

-- p=5333: a_p=+114, 4p-a_p²=8336
theorem BSD_DegreeNonneg_p5333 : BSD_FrobeniusDegreeNonneg_OPEN 5333 := fun r => by
  have hap : (a_p 5333 : ℝ) = 114 := by exact_mod_cast BSD_ap_p5333
  have key : r ^ 2 - (a_p 5333 : ℝ) * r + ((5333 : ℕ) : ℝ) =
      (r - 114/2) ^ 2 + 8336/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (114 : ℝ)/2)]

-- p=5347: a_p=+127, 4p-a_p²=5259
theorem BSD_DegreeNonneg_p5347 : BSD_FrobeniusDegreeNonneg_OPEN 5347 := fun r => by
  have hap : (a_p 5347 : ℝ) = 127 := by exact_mod_cast BSD_ap_p5347
  have key : r ^ 2 - (a_p 5347 : ℝ) * r + ((5347 : ℕ) : ℝ) =
      (r - 127/2) ^ 2 + 5259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (127 : ℝ)/2)]

-- p=5351: a_p=-5, 4p-a_p²=21379
theorem BSD_DegreeNonneg_p5351 : BSD_FrobeniusDegreeNonneg_OPEN 5351 := fun r => by
  have hap : (a_p 5351 : ℝ) = -5 := by exact_mod_cast BSD_ap_p5351
  have key : r ^ 2 - (a_p 5351 : ℝ) * r + ((5351 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 21379/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5273 : BSD_Hasse_OPEN 5273 :=
  BSD_hasse_of_degree_nonneg 5273 BSD_DegreeNonneg_p5273
theorem BSD_Hasse_OPEN_p5279 : BSD_Hasse_OPEN 5279 :=
  BSD_hasse_of_degree_nonneg 5279 BSD_DegreeNonneg_p5279
theorem BSD_Hasse_OPEN_p5281 : BSD_Hasse_OPEN 5281 :=
  BSD_hasse_of_degree_nonneg 5281 BSD_DegreeNonneg_p5281
theorem BSD_Hasse_OPEN_p5297 : BSD_Hasse_OPEN 5297 :=
  BSD_hasse_of_degree_nonneg 5297 BSD_DegreeNonneg_p5297
theorem BSD_Hasse_OPEN_p5303 : BSD_Hasse_OPEN 5303 :=
  BSD_hasse_of_degree_nonneg 5303 BSD_DegreeNonneg_p5303
theorem BSD_Hasse_OPEN_p5309 : BSD_Hasse_OPEN 5309 :=
  BSD_hasse_of_degree_nonneg 5309 BSD_DegreeNonneg_p5309
theorem BSD_Hasse_OPEN_p5323 : BSD_Hasse_OPEN 5323 :=
  BSD_hasse_of_degree_nonneg 5323 BSD_DegreeNonneg_p5323
theorem BSD_Hasse_OPEN_p5333 : BSD_Hasse_OPEN 5333 :=
  BSD_hasse_of_degree_nonneg 5333 BSD_DegreeNonneg_p5333
theorem BSD_Hasse_OPEN_p5347 : BSD_Hasse_OPEN 5347 :=
  BSD_hasse_of_degree_nonneg 5347 BSD_DegreeNonneg_p5347
theorem BSD_Hasse_OPEN_p5351 : BSD_Hasse_OPEN 5351 :=
  BSD_hasse_of_degree_nonneg 5351 BSD_DegreeNonneg_p5351

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5273 : (a_p 5273 : ℝ) ^ 2 ≤ 4 * (5273 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5273
theorem BSD_HasseBound_Disc_p5279 : (a_p 5279 : ℝ) ^ 2 ≤ 4 * (5279 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5279
theorem BSD_HasseBound_Disc_p5281 : (a_p 5281 : ℝ) ^ 2 ≤ 4 * (5281 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5281
theorem BSD_HasseBound_Disc_p5297 : (a_p 5297 : ℝ) ^ 2 ≤ 4 * (5297 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5297
theorem BSD_HasseBound_Disc_p5303 : (a_p 5303 : ℝ) ^ 2 ≤ 4 * (5303 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5303
theorem BSD_HasseBound_Disc_p5309 : (a_p 5309 : ℝ) ^ 2 ≤ 4 * (5309 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5309
theorem BSD_HasseBound_Disc_p5323 : (a_p 5323 : ℝ) ^ 2 ≤ 4 * (5323 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5323
theorem BSD_HasseBound_Disc_p5333 : (a_p 5333 : ℝ) ^ 2 ≤ 4 * (5333 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5333
theorem BSD_HasseBound_Disc_p5347 : (a_p 5347 : ℝ) ^ 2 ≤ 4 * (5347 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5347
theorem BSD_HasseBound_Disc_p5351 : (a_p 5351 : ℝ) ^ 2 ≤ 4 * (5351 : ℝ) :=
  BSD_disc_from_deg_836 BSD_DegreeNonneg_p5351

end Towers.BSD