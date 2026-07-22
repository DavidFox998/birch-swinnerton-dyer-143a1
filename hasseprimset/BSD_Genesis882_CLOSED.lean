/-
================================================================
Towers / BSD / BSD_Genesis882_CLOSED  (genesis-882)

HasseBridge Tier C: Hasse bounds for primes
9371..9433 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9371: card=9384, a_p=-12, disc=-37340
  p=9377: card=9308, a_p=+70, disc=-32608
  p=9391: card=9406, a_p=-14, disc=-37368
  p=9397: card=9221, a_p=+177, disc=-6259
  p=9403: card=9349, a_p=+55, disc=-34587
  p=9413: card=9520, a_p=-106, disc=-26416
  p=9419: card=9380, a_p=+40, disc=-36076
  p=9421: card=9536, a_p=-114, disc=-24688
  p=9431: card=9496, a_p=-64, disc=-33628
  p=9433: card=9598, a_p=-164, disc=-10836

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_882 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i882_p9371 : Fact (9371 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9377 : Fact (9377 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9391 : Fact (9391 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9397 : Fact (9397 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9403 : Fact (9403 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9413 : Fact (9413 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9419 : Fact (9419 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9421 : Fact (9421 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9431 : Fact (9431 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9433 : Fact (9433 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9371 : (E143_Finset 9371).card = 9384 := by native_decide
theorem BSD_E143_card_p9377 : (E143_Finset 9377).card = 9308 := by native_decide
theorem BSD_E143_card_p9391 : (E143_Finset 9391).card = 9406 := by native_decide
theorem BSD_E143_card_p9397 : (E143_Finset 9397).card = 9221 := by native_decide
theorem BSD_E143_card_p9403 : (E143_Finset 9403).card = 9349 := by native_decide
theorem BSD_E143_card_p9413 : (E143_Finset 9413).card = 9520 := by native_decide
theorem BSD_E143_card_p9419 : (E143_Finset 9419).card = 9380 := by native_decide
theorem BSD_E143_card_p9421 : (E143_Finset 9421).card = 9536 := by native_decide
theorem BSD_E143_card_p9431 : (E143_Finset 9431).card = 9496 := by native_decide
theorem BSD_E143_card_p9433 : (E143_Finset 9433).card = 9598 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9371 : a_p 9371 = (-12 : ℤ) := by
  have h := BSD_E143_card_p9371; unfold a_p; omega
theorem BSD_ap_p9377 : a_p 9377 = (70 : ℤ) := by
  have h := BSD_E143_card_p9377; unfold a_p; omega
theorem BSD_ap_p9391 : a_p 9391 = (-14 : ℤ) := by
  have h := BSD_E143_card_p9391; unfold a_p; omega
theorem BSD_ap_p9397 : a_p 9397 = (177 : ℤ) := by
  have h := BSD_E143_card_p9397; unfold a_p; omega
theorem BSD_ap_p9403 : a_p 9403 = (55 : ℤ) := by
  have h := BSD_E143_card_p9403; unfold a_p; omega
theorem BSD_ap_p9413 : a_p 9413 = (-106 : ℤ) := by
  have h := BSD_E143_card_p9413; unfold a_p; omega
theorem BSD_ap_p9419 : a_p 9419 = (40 : ℤ) := by
  have h := BSD_E143_card_p9419; unfold a_p; omega
theorem BSD_ap_p9421 : a_p 9421 = (-114 : ℤ) := by
  have h := BSD_E143_card_p9421; unfold a_p; omega
theorem BSD_ap_p9431 : a_p 9431 = (-64 : ℤ) := by
  have h := BSD_E143_card_p9431; unfold a_p; omega
theorem BSD_ap_p9433 : a_p 9433 = (-164 : ℤ) := by
  have h := BSD_E143_card_p9433; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9371: a_p=-12, 4p-a_p²=37340
theorem BSD_DegreeNonneg_p9371 : BSD_FrobeniusDegreeNonneg_OPEN 9371 := fun r => by
  have hap : (a_p 9371 : ℝ) = -12 := by exact_mod_cast BSD_ap_p9371
  have key : r ^ 2 - (a_p 9371 : ℝ) * r + ((9371 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 37340/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

-- p=9377: a_p=+70, 4p-a_p²=32608
theorem BSD_DegreeNonneg_p9377 : BSD_FrobeniusDegreeNonneg_OPEN 9377 := fun r => by
  have hap : (a_p 9377 : ℝ) = 70 := by exact_mod_cast BSD_ap_p9377
  have key : r ^ 2 - (a_p 9377 : ℝ) * r + ((9377 : ℕ) : ℝ) =
      (r - 70/2) ^ 2 + 32608/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (70 : ℝ)/2)]

-- p=9391: a_p=-14, 4p-a_p²=37368
theorem BSD_DegreeNonneg_p9391 : BSD_FrobeniusDegreeNonneg_OPEN 9391 := fun r => by
  have hap : (a_p 9391 : ℝ) = -14 := by exact_mod_cast BSD_ap_p9391
  have key : r ^ 2 - (a_p 9391 : ℝ) * r + ((9391 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 37368/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

-- p=9397: a_p=+177, 4p-a_p²=6259
theorem BSD_DegreeNonneg_p9397 : BSD_FrobeniusDegreeNonneg_OPEN 9397 := fun r => by
  have hap : (a_p 9397 : ℝ) = 177 := by exact_mod_cast BSD_ap_p9397
  have key : r ^ 2 - (a_p 9397 : ℝ) * r + ((9397 : ℕ) : ℝ) =
      (r - 177/2) ^ 2 + 6259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (177 : ℝ)/2)]

-- p=9403: a_p=+55, 4p-a_p²=34587
theorem BSD_DegreeNonneg_p9403 : BSD_FrobeniusDegreeNonneg_OPEN 9403 := fun r => by
  have hap : (a_p 9403 : ℝ) = 55 := by exact_mod_cast BSD_ap_p9403
  have key : r ^ 2 - (a_p 9403 : ℝ) * r + ((9403 : ℕ) : ℝ) =
      (r - 55/2) ^ 2 + 34587/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (55 : ℝ)/2)]

-- p=9413: a_p=-106, 4p-a_p²=26416
theorem BSD_DegreeNonneg_p9413 : BSD_FrobeniusDegreeNonneg_OPEN 9413 := fun r => by
  have hap : (a_p 9413 : ℝ) = -106 := by exact_mod_cast BSD_ap_p9413
  have key : r ^ 2 - (a_p 9413 : ℝ) * r + ((9413 : ℕ) : ℝ) =
      (r + 106/2) ^ 2 + 26416/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (106 : ℝ)/2)]

-- p=9419: a_p=+40, 4p-a_p²=36076
theorem BSD_DegreeNonneg_p9419 : BSD_FrobeniusDegreeNonneg_OPEN 9419 := fun r => by
  have hap : (a_p 9419 : ℝ) = 40 := by exact_mod_cast BSD_ap_p9419
  have key : r ^ 2 - (a_p 9419 : ℝ) * r + ((9419 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 36076/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

-- p=9421: a_p=-114, 4p-a_p²=24688
theorem BSD_DegreeNonneg_p9421 : BSD_FrobeniusDegreeNonneg_OPEN 9421 := fun r => by
  have hap : (a_p 9421 : ℝ) = -114 := by exact_mod_cast BSD_ap_p9421
  have key : r ^ 2 - (a_p 9421 : ℝ) * r + ((9421 : ℕ) : ℝ) =
      (r + 114/2) ^ 2 + 24688/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (114 : ℝ)/2)]

-- p=9431: a_p=-64, 4p-a_p²=33628
theorem BSD_DegreeNonneg_p9431 : BSD_FrobeniusDegreeNonneg_OPEN 9431 := fun r => by
  have hap : (a_p 9431 : ℝ) = -64 := by exact_mod_cast BSD_ap_p9431
  have key : r ^ 2 - (a_p 9431 : ℝ) * r + ((9431 : ℕ) : ℝ) =
      (r + 64/2) ^ 2 + 33628/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (64 : ℝ)/2)]

-- p=9433: a_p=-164, 4p-a_p²=10836
theorem BSD_DegreeNonneg_p9433 : BSD_FrobeniusDegreeNonneg_OPEN 9433 := fun r => by
  have hap : (a_p 9433 : ℝ) = -164 := by exact_mod_cast BSD_ap_p9433
  have key : r ^ 2 - (a_p 9433 : ℝ) * r + ((9433 : ℕ) : ℝ) =
      (r + 164/2) ^ 2 + 10836/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (164 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9371 : BSD_Hasse_OPEN 9371 :=
  BSD_hasse_of_degree_nonneg 9371 BSD_DegreeNonneg_p9371
theorem BSD_Hasse_OPEN_p9377 : BSD_Hasse_OPEN 9377 :=
  BSD_hasse_of_degree_nonneg 9377 BSD_DegreeNonneg_p9377
theorem BSD_Hasse_OPEN_p9391 : BSD_Hasse_OPEN 9391 :=
  BSD_hasse_of_degree_nonneg 9391 BSD_DegreeNonneg_p9391
theorem BSD_Hasse_OPEN_p9397 : BSD_Hasse_OPEN 9397 :=
  BSD_hasse_of_degree_nonneg 9397 BSD_DegreeNonneg_p9397
theorem BSD_Hasse_OPEN_p9403 : BSD_Hasse_OPEN 9403 :=
  BSD_hasse_of_degree_nonneg 9403 BSD_DegreeNonneg_p9403
theorem BSD_Hasse_OPEN_p9413 : BSD_Hasse_OPEN 9413 :=
  BSD_hasse_of_degree_nonneg 9413 BSD_DegreeNonneg_p9413
theorem BSD_Hasse_OPEN_p9419 : BSD_Hasse_OPEN 9419 :=
  BSD_hasse_of_degree_nonneg 9419 BSD_DegreeNonneg_p9419
theorem BSD_Hasse_OPEN_p9421 : BSD_Hasse_OPEN 9421 :=
  BSD_hasse_of_degree_nonneg 9421 BSD_DegreeNonneg_p9421
theorem BSD_Hasse_OPEN_p9431 : BSD_Hasse_OPEN 9431 :=
  BSD_hasse_of_degree_nonneg 9431 BSD_DegreeNonneg_p9431
theorem BSD_Hasse_OPEN_p9433 : BSD_Hasse_OPEN 9433 :=
  BSD_hasse_of_degree_nonneg 9433 BSD_DegreeNonneg_p9433

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9371 : (a_p 9371 : ℝ) ^ 2 ≤ 4 * (9371 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9371
theorem BSD_HasseBound_Disc_p9377 : (a_p 9377 : ℝ) ^ 2 ≤ 4 * (9377 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9377
theorem BSD_HasseBound_Disc_p9391 : (a_p 9391 : ℝ) ^ 2 ≤ 4 * (9391 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9391
theorem BSD_HasseBound_Disc_p9397 : (a_p 9397 : ℝ) ^ 2 ≤ 4 * (9397 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9397
theorem BSD_HasseBound_Disc_p9403 : (a_p 9403 : ℝ) ^ 2 ≤ 4 * (9403 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9403
theorem BSD_HasseBound_Disc_p9413 : (a_p 9413 : ℝ) ^ 2 ≤ 4 * (9413 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9413
theorem BSD_HasseBound_Disc_p9419 : (a_p 9419 : ℝ) ^ 2 ≤ 4 * (9419 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9419
theorem BSD_HasseBound_Disc_p9421 : (a_p 9421 : ℝ) ^ 2 ≤ 4 * (9421 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9421
theorem BSD_HasseBound_Disc_p9431 : (a_p 9431 : ℝ) ^ 2 ≤ 4 * (9431 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9431
theorem BSD_HasseBound_Disc_p9433 : (a_p 9433 : ℝ) ^ 2 ≤ 4 * (9433 : ℝ) :=
  BSD_disc_from_deg_882 BSD_DegreeNonneg_p9433

end Towers.BSD