/-
================================================================
Towers / BSD / BSD_Genesis847_CLOSED  (genesis-847)

HasseBridge Tier C: Hasse bounds for primes
6217..6287 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6217: card=6276, a_p=-58, disc=-21504
  p=6221: card=6252, a_p=-30, disc=-23984
  p=6229: card=6279, a_p=-49, disc=-22515
  p=6247: card=6286, a_p=-38, disc=-23544
  p=6257: card=6277, a_p=-19, disc=-24667
  p=6263: card=6257, a_p=+7, disc=-25003
  p=6269: card=6180, a_p=+90, disc=-16976
  p=6271: card=6287, a_p=-15, disc=-24859
  p=6277: card=6300, a_p=-22, disc=-24624
  p=6287: card=6162, a_p=+126, disc=-9272

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_847 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i847_p6217 : Fact (6217 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6221 : Fact (6221 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6229 : Fact (6229 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6247 : Fact (6247 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6257 : Fact (6257 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6263 : Fact (6263 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6269 : Fact (6269 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6271 : Fact (6271 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6277 : Fact (6277 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6287 : Fact (6287 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6217 : (E143_Finset 6217).card = 6276 := by native_decide
theorem BSD_E143_card_p6221 : (E143_Finset 6221).card = 6252 := by native_decide
theorem BSD_E143_card_p6229 : (E143_Finset 6229).card = 6279 := by native_decide
theorem BSD_E143_card_p6247 : (E143_Finset 6247).card = 6286 := by native_decide
theorem BSD_E143_card_p6257 : (E143_Finset 6257).card = 6277 := by native_decide
theorem BSD_E143_card_p6263 : (E143_Finset 6263).card = 6257 := by native_decide
theorem BSD_E143_card_p6269 : (E143_Finset 6269).card = 6180 := by native_decide
theorem BSD_E143_card_p6271 : (E143_Finset 6271).card = 6287 := by native_decide
theorem BSD_E143_card_p6277 : (E143_Finset 6277).card = 6300 := by native_decide
theorem BSD_E143_card_p6287 : (E143_Finset 6287).card = 6162 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6217 : a_p 6217 = (-58 : ℤ) := by
  have h := BSD_E143_card_p6217; unfold a_p; omega
theorem BSD_ap_p6221 : a_p 6221 = (-30 : ℤ) := by
  have h := BSD_E143_card_p6221; unfold a_p; omega
theorem BSD_ap_p6229 : a_p 6229 = (-49 : ℤ) := by
  have h := BSD_E143_card_p6229; unfold a_p; omega
theorem BSD_ap_p6247 : a_p 6247 = (-38 : ℤ) := by
  have h := BSD_E143_card_p6247; unfold a_p; omega
theorem BSD_ap_p6257 : a_p 6257 = (-19 : ℤ) := by
  have h := BSD_E143_card_p6257; unfold a_p; omega
theorem BSD_ap_p6263 : a_p 6263 = (7 : ℤ) := by
  have h := BSD_E143_card_p6263; unfold a_p; omega
theorem BSD_ap_p6269 : a_p 6269 = (90 : ℤ) := by
  have h := BSD_E143_card_p6269; unfold a_p; omega
theorem BSD_ap_p6271 : a_p 6271 = (-15 : ℤ) := by
  have h := BSD_E143_card_p6271; unfold a_p; omega
theorem BSD_ap_p6277 : a_p 6277 = (-22 : ℤ) := by
  have h := BSD_E143_card_p6277; unfold a_p; omega
theorem BSD_ap_p6287 : a_p 6287 = (126 : ℤ) := by
  have h := BSD_E143_card_p6287; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6217: a_p=-58, 4p-a_p²=21504
theorem BSD_DegreeNonneg_p6217 : BSD_FrobeniusDegreeNonneg_OPEN 6217 := fun r => by
  have hap : (a_p 6217 : ℝ) = -58 := by exact_mod_cast BSD_ap_p6217
  have key : r ^ 2 - (a_p 6217 : ℝ) * r + ((6217 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 21504/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=6221: a_p=-30, 4p-a_p²=23984
theorem BSD_DegreeNonneg_p6221 : BSD_FrobeniusDegreeNonneg_OPEN 6221 := fun r => by
  have hap : (a_p 6221 : ℝ) = -30 := by exact_mod_cast BSD_ap_p6221
  have key : r ^ 2 - (a_p 6221 : ℝ) * r + ((6221 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 23984/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

-- p=6229: a_p=-49, 4p-a_p²=22515
theorem BSD_DegreeNonneg_p6229 : BSD_FrobeniusDegreeNonneg_OPEN 6229 := fun r => by
  have hap : (a_p 6229 : ℝ) = -49 := by exact_mod_cast BSD_ap_p6229
  have key : r ^ 2 - (a_p 6229 : ℝ) * r + ((6229 : ℕ) : ℝ) =
      (r + 49/2) ^ 2 + 22515/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (49 : ℝ)/2)]

-- p=6247: a_p=-38, 4p-a_p²=23544
theorem BSD_DegreeNonneg_p6247 : BSD_FrobeniusDegreeNonneg_OPEN 6247 := fun r => by
  have hap : (a_p 6247 : ℝ) = -38 := by exact_mod_cast BSD_ap_p6247
  have key : r ^ 2 - (a_p 6247 : ℝ) * r + ((6247 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 23544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

-- p=6257: a_p=-19, 4p-a_p²=24667
theorem BSD_DegreeNonneg_p6257 : BSD_FrobeniusDegreeNonneg_OPEN 6257 := fun r => by
  have hap : (a_p 6257 : ℝ) = -19 := by exact_mod_cast BSD_ap_p6257
  have key : r ^ 2 - (a_p 6257 : ℝ) * r + ((6257 : ℕ) : ℝ) =
      (r + 19/2) ^ 2 + 24667/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (19 : ℝ)/2)]

-- p=6263: a_p=+7, 4p-a_p²=25003
theorem BSD_DegreeNonneg_p6263 : BSD_FrobeniusDegreeNonneg_OPEN 6263 := fun r => by
  have hap : (a_p 6263 : ℝ) = 7 := by exact_mod_cast BSD_ap_p6263
  have key : r ^ 2 - (a_p 6263 : ℝ) * r + ((6263 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 25003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

-- p=6269: a_p=+90, 4p-a_p²=16976
theorem BSD_DegreeNonneg_p6269 : BSD_FrobeniusDegreeNonneg_OPEN 6269 := fun r => by
  have hap : (a_p 6269 : ℝ) = 90 := by exact_mod_cast BSD_ap_p6269
  have key : r ^ 2 - (a_p 6269 : ℝ) * r + ((6269 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 16976/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

-- p=6271: a_p=-15, 4p-a_p²=24859
theorem BSD_DegreeNonneg_p6271 : BSD_FrobeniusDegreeNonneg_OPEN 6271 := fun r => by
  have hap : (a_p 6271 : ℝ) = -15 := by exact_mod_cast BSD_ap_p6271
  have key : r ^ 2 - (a_p 6271 : ℝ) * r + ((6271 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 24859/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

-- p=6277: a_p=-22, 4p-a_p²=24624
theorem BSD_DegreeNonneg_p6277 : BSD_FrobeniusDegreeNonneg_OPEN 6277 := fun r => by
  have hap : (a_p 6277 : ℝ) = -22 := by exact_mod_cast BSD_ap_p6277
  have key : r ^ 2 - (a_p 6277 : ℝ) * r + ((6277 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 24624/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=6287: a_p=+126, 4p-a_p²=9272
theorem BSD_DegreeNonneg_p6287 : BSD_FrobeniusDegreeNonneg_OPEN 6287 := fun r => by
  have hap : (a_p 6287 : ℝ) = 126 := by exact_mod_cast BSD_ap_p6287
  have key : r ^ 2 - (a_p 6287 : ℝ) * r + ((6287 : ℕ) : ℝ) =
      (r - 126/2) ^ 2 + 9272/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (126 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6217 : BSD_Hasse_OPEN 6217 :=
  BSD_hasse_of_degree_nonneg 6217 BSD_DegreeNonneg_p6217
theorem BSD_Hasse_OPEN_p6221 : BSD_Hasse_OPEN 6221 :=
  BSD_hasse_of_degree_nonneg 6221 BSD_DegreeNonneg_p6221
theorem BSD_Hasse_OPEN_p6229 : BSD_Hasse_OPEN 6229 :=
  BSD_hasse_of_degree_nonneg 6229 BSD_DegreeNonneg_p6229
theorem BSD_Hasse_OPEN_p6247 : BSD_Hasse_OPEN 6247 :=
  BSD_hasse_of_degree_nonneg 6247 BSD_DegreeNonneg_p6247
theorem BSD_Hasse_OPEN_p6257 : BSD_Hasse_OPEN 6257 :=
  BSD_hasse_of_degree_nonneg 6257 BSD_DegreeNonneg_p6257
theorem BSD_Hasse_OPEN_p6263 : BSD_Hasse_OPEN 6263 :=
  BSD_hasse_of_degree_nonneg 6263 BSD_DegreeNonneg_p6263
theorem BSD_Hasse_OPEN_p6269 : BSD_Hasse_OPEN 6269 :=
  BSD_hasse_of_degree_nonneg 6269 BSD_DegreeNonneg_p6269
theorem BSD_Hasse_OPEN_p6271 : BSD_Hasse_OPEN 6271 :=
  BSD_hasse_of_degree_nonneg 6271 BSD_DegreeNonneg_p6271
theorem BSD_Hasse_OPEN_p6277 : BSD_Hasse_OPEN 6277 :=
  BSD_hasse_of_degree_nonneg 6277 BSD_DegreeNonneg_p6277
theorem BSD_Hasse_OPEN_p6287 : BSD_Hasse_OPEN 6287 :=
  BSD_hasse_of_degree_nonneg 6287 BSD_DegreeNonneg_p6287

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6217 : (a_p 6217 : ℝ) ^ 2 ≤ 4 * (6217 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6217
theorem BSD_HasseBound_Disc_p6221 : (a_p 6221 : ℝ) ^ 2 ≤ 4 * (6221 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6221
theorem BSD_HasseBound_Disc_p6229 : (a_p 6229 : ℝ) ^ 2 ≤ 4 * (6229 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6229
theorem BSD_HasseBound_Disc_p6247 : (a_p 6247 : ℝ) ^ 2 ≤ 4 * (6247 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6247
theorem BSD_HasseBound_Disc_p6257 : (a_p 6257 : ℝ) ^ 2 ≤ 4 * (6257 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6257
theorem BSD_HasseBound_Disc_p6263 : (a_p 6263 : ℝ) ^ 2 ≤ 4 * (6263 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6263
theorem BSD_HasseBound_Disc_p6269 : (a_p 6269 : ℝ) ^ 2 ≤ 4 * (6269 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6269
theorem BSD_HasseBound_Disc_p6271 : (a_p 6271 : ℝ) ^ 2 ≤ 4 * (6271 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6271
theorem BSD_HasseBound_Disc_p6277 : (a_p 6277 : ℝ) ^ 2 ≤ 4 * (6277 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6277
theorem BSD_HasseBound_Disc_p6287 : (a_p 6287 : ℝ) ^ 2 ≤ 4 * (6287 : ℝ) :=
  BSD_disc_from_deg_847 BSD_DegreeNonneg_p6287

end Towers.BSD