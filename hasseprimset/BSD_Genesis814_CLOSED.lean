/-
================================================================
Towers / BSD / BSD_Genesis814_CLOSED  (genesis-814)

HasseBridge Tier C: Hasse bounds for primes
3407..3491 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3407: card=3314, a_p=+94, disc=-4792
  p=3413: card=3323, a_p=+91, disc=-5371
  p=3433: card=3420, a_p=+14, disc=-13536
  p=3449: card=3366, a_p=+84, disc=-6740
  p=3457: card=3463, a_p=-5, disc=-13803
  p=3461: card=3446, a_p=+16, disc=-13588
  p=3463: card=3496, a_p=-32, disc=-12828
  p=3467: card=3466, a_p=+2, disc=-13864
  p=3469: card=3433, a_p=+37, disc=-12507
  p=3491: card=3581, a_p=-89, disc=-6043

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_814 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i814_p3407 : Fact (3407 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3413 : Fact (3413 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3433 : Fact (3433 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3449 : Fact (3449 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3457 : Fact (3457 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3461 : Fact (3461 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3463 : Fact (3463 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3467 : Fact (3467 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3469 : Fact (3469 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3491 : Fact (3491 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3407 : (E143_Finset 3407).card = 3314 := by native_decide
theorem BSD_E143_card_p3413 : (E143_Finset 3413).card = 3323 := by native_decide
theorem BSD_E143_card_p3433 : (E143_Finset 3433).card = 3420 := by native_decide
theorem BSD_E143_card_p3449 : (E143_Finset 3449).card = 3366 := by native_decide
theorem BSD_E143_card_p3457 : (E143_Finset 3457).card = 3463 := by native_decide
theorem BSD_E143_card_p3461 : (E143_Finset 3461).card = 3446 := by native_decide
theorem BSD_E143_card_p3463 : (E143_Finset 3463).card = 3496 := by native_decide
theorem BSD_E143_card_p3467 : (E143_Finset 3467).card = 3466 := by native_decide
theorem BSD_E143_card_p3469 : (E143_Finset 3469).card = 3433 := by native_decide
theorem BSD_E143_card_p3491 : (E143_Finset 3491).card = 3581 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3407 : a_p 3407 = (94 : ℤ) := by
  have h := BSD_E143_card_p3407; unfold a_p; omega
theorem BSD_ap_p3413 : a_p 3413 = (91 : ℤ) := by
  have h := BSD_E143_card_p3413; unfold a_p; omega
theorem BSD_ap_p3433 : a_p 3433 = (14 : ℤ) := by
  have h := BSD_E143_card_p3433; unfold a_p; omega
theorem BSD_ap_p3449 : a_p 3449 = (84 : ℤ) := by
  have h := BSD_E143_card_p3449; unfold a_p; omega
theorem BSD_ap_p3457 : a_p 3457 = (-5 : ℤ) := by
  have h := BSD_E143_card_p3457; unfold a_p; omega
theorem BSD_ap_p3461 : a_p 3461 = (16 : ℤ) := by
  have h := BSD_E143_card_p3461; unfold a_p; omega
theorem BSD_ap_p3463 : a_p 3463 = (-32 : ℤ) := by
  have h := BSD_E143_card_p3463; unfold a_p; omega
theorem BSD_ap_p3467 : a_p 3467 = (2 : ℤ) := by
  have h := BSD_E143_card_p3467; unfold a_p; omega
theorem BSD_ap_p3469 : a_p 3469 = (37 : ℤ) := by
  have h := BSD_E143_card_p3469; unfold a_p; omega
theorem BSD_ap_p3491 : a_p 3491 = (-89 : ℤ) := by
  have h := BSD_E143_card_p3491; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3407: a_p=+94, 4p-a_p²=4792
theorem BSD_DegreeNonneg_p3407 : BSD_FrobeniusDegreeNonneg_OPEN 3407 := fun r => by
  have hap : (a_p 3407 : ℝ) = 94 := by exact_mod_cast BSD_ap_p3407
  have key : r ^ 2 - (a_p 3407 : ℝ) * r + ((3407 : ℕ) : ℝ) =
      (r - 94/2) ^ 2 + 4792/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (94 : ℝ)/2)]

-- p=3413: a_p=+91, 4p-a_p²=5371
theorem BSD_DegreeNonneg_p3413 : BSD_FrobeniusDegreeNonneg_OPEN 3413 := fun r => by
  have hap : (a_p 3413 : ℝ) = 91 := by exact_mod_cast BSD_ap_p3413
  have key : r ^ 2 - (a_p 3413 : ℝ) * r + ((3413 : ℕ) : ℝ) =
      (r - 91/2) ^ 2 + 5371/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (91 : ℝ)/2)]

-- p=3433: a_p=+14, 4p-a_p²=13536
theorem BSD_DegreeNonneg_p3433 : BSD_FrobeniusDegreeNonneg_OPEN 3433 := fun r => by
  have hap : (a_p 3433 : ℝ) = 14 := by exact_mod_cast BSD_ap_p3433
  have key : r ^ 2 - (a_p 3433 : ℝ) * r + ((3433 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 13536/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

-- p=3449: a_p=+84, 4p-a_p²=6740
theorem BSD_DegreeNonneg_p3449 : BSD_FrobeniusDegreeNonneg_OPEN 3449 := fun r => by
  have hap : (a_p 3449 : ℝ) = 84 := by exact_mod_cast BSD_ap_p3449
  have key : r ^ 2 - (a_p 3449 : ℝ) * r + ((3449 : ℕ) : ℝ) =
      (r - 84/2) ^ 2 + 6740/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (84 : ℝ)/2)]

-- p=3457: a_p=-5, 4p-a_p²=13803
theorem BSD_DegreeNonneg_p3457 : BSD_FrobeniusDegreeNonneg_OPEN 3457 := fun r => by
  have hap : (a_p 3457 : ℝ) = -5 := by exact_mod_cast BSD_ap_p3457
  have key : r ^ 2 - (a_p 3457 : ℝ) * r + ((3457 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 13803/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

-- p=3461: a_p=+16, 4p-a_p²=13588
theorem BSD_DegreeNonneg_p3461 : BSD_FrobeniusDegreeNonneg_OPEN 3461 := fun r => by
  have hap : (a_p 3461 : ℝ) = 16 := by exact_mod_cast BSD_ap_p3461
  have key : r ^ 2 - (a_p 3461 : ℝ) * r + ((3461 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 13588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

-- p=3463: a_p=-32, 4p-a_p²=12828
theorem BSD_DegreeNonneg_p3463 : BSD_FrobeniusDegreeNonneg_OPEN 3463 := fun r => by
  have hap : (a_p 3463 : ℝ) = -32 := by exact_mod_cast BSD_ap_p3463
  have key : r ^ 2 - (a_p 3463 : ℝ) * r + ((3463 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 12828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=3467: a_p=+2, 4p-a_p²=13864
theorem BSD_DegreeNonneg_p3467 : BSD_FrobeniusDegreeNonneg_OPEN 3467 := fun r => by
  have hap : (a_p 3467 : ℝ) = 2 := by exact_mod_cast BSD_ap_p3467
  have key : r ^ 2 - (a_p 3467 : ℝ) * r + ((3467 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 13864/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

-- p=3469: a_p=+37, 4p-a_p²=12507
theorem BSD_DegreeNonneg_p3469 : BSD_FrobeniusDegreeNonneg_OPEN 3469 := fun r => by
  have hap : (a_p 3469 : ℝ) = 37 := by exact_mod_cast BSD_ap_p3469
  have key : r ^ 2 - (a_p 3469 : ℝ) * r + ((3469 : ℕ) : ℝ) =
      (r - 37/2) ^ 2 + 12507/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (37 : ℝ)/2)]

-- p=3491: a_p=-89, 4p-a_p²=6043
theorem BSD_DegreeNonneg_p3491 : BSD_FrobeniusDegreeNonneg_OPEN 3491 := fun r => by
  have hap : (a_p 3491 : ℝ) = -89 := by exact_mod_cast BSD_ap_p3491
  have key : r ^ 2 - (a_p 3491 : ℝ) * r + ((3491 : ℕ) : ℝ) =
      (r + 89/2) ^ 2 + 6043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (89 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3407 : BSD_Hasse_OPEN 3407 :=
  BSD_hasse_of_degree_nonneg 3407 BSD_DegreeNonneg_p3407
theorem BSD_Hasse_OPEN_p3413 : BSD_Hasse_OPEN 3413 :=
  BSD_hasse_of_degree_nonneg 3413 BSD_DegreeNonneg_p3413
theorem BSD_Hasse_OPEN_p3433 : BSD_Hasse_OPEN 3433 :=
  BSD_hasse_of_degree_nonneg 3433 BSD_DegreeNonneg_p3433
theorem BSD_Hasse_OPEN_p3449 : BSD_Hasse_OPEN 3449 :=
  BSD_hasse_of_degree_nonneg 3449 BSD_DegreeNonneg_p3449
theorem BSD_Hasse_OPEN_p3457 : BSD_Hasse_OPEN 3457 :=
  BSD_hasse_of_degree_nonneg 3457 BSD_DegreeNonneg_p3457
theorem BSD_Hasse_OPEN_p3461 : BSD_Hasse_OPEN 3461 :=
  BSD_hasse_of_degree_nonneg 3461 BSD_DegreeNonneg_p3461
theorem BSD_Hasse_OPEN_p3463 : BSD_Hasse_OPEN 3463 :=
  BSD_hasse_of_degree_nonneg 3463 BSD_DegreeNonneg_p3463
theorem BSD_Hasse_OPEN_p3467 : BSD_Hasse_OPEN 3467 :=
  BSD_hasse_of_degree_nonneg 3467 BSD_DegreeNonneg_p3467
theorem BSD_Hasse_OPEN_p3469 : BSD_Hasse_OPEN 3469 :=
  BSD_hasse_of_degree_nonneg 3469 BSD_DegreeNonneg_p3469
theorem BSD_Hasse_OPEN_p3491 : BSD_Hasse_OPEN 3491 :=
  BSD_hasse_of_degree_nonneg 3491 BSD_DegreeNonneg_p3491

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3407 : (a_p 3407 : ℝ) ^ 2 ≤ 4 * (3407 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3407
theorem BSD_HasseBound_Disc_p3413 : (a_p 3413 : ℝ) ^ 2 ≤ 4 * (3413 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3413
theorem BSD_HasseBound_Disc_p3433 : (a_p 3433 : ℝ) ^ 2 ≤ 4 * (3433 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3433
theorem BSD_HasseBound_Disc_p3449 : (a_p 3449 : ℝ) ^ 2 ≤ 4 * (3449 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3449
theorem BSD_HasseBound_Disc_p3457 : (a_p 3457 : ℝ) ^ 2 ≤ 4 * (3457 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3457
theorem BSD_HasseBound_Disc_p3461 : (a_p 3461 : ℝ) ^ 2 ≤ 4 * (3461 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3461
theorem BSD_HasseBound_Disc_p3463 : (a_p 3463 : ℝ) ^ 2 ≤ 4 * (3463 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3463
theorem BSD_HasseBound_Disc_p3467 : (a_p 3467 : ℝ) ^ 2 ≤ 4 * (3467 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3467
theorem BSD_HasseBound_Disc_p3469 : (a_p 3469 : ℝ) ^ 2 ≤ 4 * (3469 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3469
theorem BSD_HasseBound_Disc_p3491 : (a_p 3491 : ℝ) ^ 2 ≤ 4 * (3491 : ℝ) :=
  BSD_disc_from_deg_814 BSD_DegreeNonneg_p3491

end Towers.BSD