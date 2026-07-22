/-
================================================================
Towers / BSD / BSD_Genesis816_CLOSED  (genesis-816)

HasseBridge Tier C: Hasse bounds for primes
3559..3631 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3559: card=3576, a_p=-16, disc=-13980
  p=3571: card=3690, a_p=-118, disc=-360
  p=3581: card=3678, a_p=-96, disc=-5108
  p=3583: card=3534, a_p=+50, disc=-11832
  p=3593: card=3518, a_p=+76, disc=-8596
  p=3607: card=3566, a_p=+42, disc=-12664
  p=3613: card=3600, a_p=+14, disc=-14256
  p=3617: card=3675, a_p=-57, disc=-11219
  p=3623: card=3576, a_p=+48, disc=-12188
  p=3631: card=3584, a_p=+48, disc=-12220

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_816 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i816_p3559 : Fact (3559 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3571 : Fact (3571 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3581 : Fact (3581 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3583 : Fact (3583 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3593 : Fact (3593 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3607 : Fact (3607 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3613 : Fact (3613 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3617 : Fact (3617 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3623 : Fact (3623 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3631 : Fact (3631 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3559 : (E143_Finset 3559).card = 3576 := by native_decide
theorem BSD_E143_card_p3571 : (E143_Finset 3571).card = 3690 := by native_decide
theorem BSD_E143_card_p3581 : (E143_Finset 3581).card = 3678 := by native_decide
theorem BSD_E143_card_p3583 : (E143_Finset 3583).card = 3534 := by native_decide
theorem BSD_E143_card_p3593 : (E143_Finset 3593).card = 3518 := by native_decide
theorem BSD_E143_card_p3607 : (E143_Finset 3607).card = 3566 := by native_decide
theorem BSD_E143_card_p3613 : (E143_Finset 3613).card = 3600 := by native_decide
theorem BSD_E143_card_p3617 : (E143_Finset 3617).card = 3675 := by native_decide
theorem BSD_E143_card_p3623 : (E143_Finset 3623).card = 3576 := by native_decide
theorem BSD_E143_card_p3631 : (E143_Finset 3631).card = 3584 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3559 : a_p 3559 = (-16 : ℤ) := by
  have h := BSD_E143_card_p3559; unfold a_p; omega
theorem BSD_ap_p3571 : a_p 3571 = (-118 : ℤ) := by
  have h := BSD_E143_card_p3571; unfold a_p; omega
theorem BSD_ap_p3581 : a_p 3581 = (-96 : ℤ) := by
  have h := BSD_E143_card_p3581; unfold a_p; omega
theorem BSD_ap_p3583 : a_p 3583 = (50 : ℤ) := by
  have h := BSD_E143_card_p3583; unfold a_p; omega
theorem BSD_ap_p3593 : a_p 3593 = (76 : ℤ) := by
  have h := BSD_E143_card_p3593; unfold a_p; omega
theorem BSD_ap_p3607 : a_p 3607 = (42 : ℤ) := by
  have h := BSD_E143_card_p3607; unfold a_p; omega
theorem BSD_ap_p3613 : a_p 3613 = (14 : ℤ) := by
  have h := BSD_E143_card_p3613; unfold a_p; omega
theorem BSD_ap_p3617 : a_p 3617 = (-57 : ℤ) := by
  have h := BSD_E143_card_p3617; unfold a_p; omega
theorem BSD_ap_p3623 : a_p 3623 = (48 : ℤ) := by
  have h := BSD_E143_card_p3623; unfold a_p; omega
theorem BSD_ap_p3631 : a_p 3631 = (48 : ℤ) := by
  have h := BSD_E143_card_p3631; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3559: a_p=-16, 4p-a_p²=13980
theorem BSD_DegreeNonneg_p3559 : BSD_FrobeniusDegreeNonneg_OPEN 3559 := fun r => by
  have hap : (a_p 3559 : ℝ) = -16 := by exact_mod_cast BSD_ap_p3559
  have key : r ^ 2 - (a_p 3559 : ℝ) * r + ((3559 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 13980/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

-- p=3571: a_p=-118, 4p-a_p²=360
theorem BSD_DegreeNonneg_p3571 : BSD_FrobeniusDegreeNonneg_OPEN 3571 := fun r => by
  have hap : (a_p 3571 : ℝ) = -118 := by exact_mod_cast BSD_ap_p3571
  have key : r ^ 2 - (a_p 3571 : ℝ) * r + ((3571 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 360/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

-- p=3581: a_p=-96, 4p-a_p²=5108
theorem BSD_DegreeNonneg_p3581 : BSD_FrobeniusDegreeNonneg_OPEN 3581 := fun r => by
  have hap : (a_p 3581 : ℝ) = -96 := by exact_mod_cast BSD_ap_p3581
  have key : r ^ 2 - (a_p 3581 : ℝ) * r + ((3581 : ℕ) : ℝ) =
      (r + 96/2) ^ 2 + 5108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (96 : ℝ)/2)]

-- p=3583: a_p=+50, 4p-a_p²=11832
theorem BSD_DegreeNonneg_p3583 : BSD_FrobeniusDegreeNonneg_OPEN 3583 := fun r => by
  have hap : (a_p 3583 : ℝ) = 50 := by exact_mod_cast BSD_ap_p3583
  have key : r ^ 2 - (a_p 3583 : ℝ) * r + ((3583 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 11832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

-- p=3593: a_p=+76, 4p-a_p²=8596
theorem BSD_DegreeNonneg_p3593 : BSD_FrobeniusDegreeNonneg_OPEN 3593 := fun r => by
  have hap : (a_p 3593 : ℝ) = 76 := by exact_mod_cast BSD_ap_p3593
  have key : r ^ 2 - (a_p 3593 : ℝ) * r + ((3593 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 8596/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

-- p=3607: a_p=+42, 4p-a_p²=12664
theorem BSD_DegreeNonneg_p3607 : BSD_FrobeniusDegreeNonneg_OPEN 3607 := fun r => by
  have hap : (a_p 3607 : ℝ) = 42 := by exact_mod_cast BSD_ap_p3607
  have key : r ^ 2 - (a_p 3607 : ℝ) * r + ((3607 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 12664/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

-- p=3613: a_p=+14, 4p-a_p²=14256
theorem BSD_DegreeNonneg_p3613 : BSD_FrobeniusDegreeNonneg_OPEN 3613 := fun r => by
  have hap : (a_p 3613 : ℝ) = 14 := by exact_mod_cast BSD_ap_p3613
  have key : r ^ 2 - (a_p 3613 : ℝ) * r + ((3613 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 14256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

-- p=3617: a_p=-57, 4p-a_p²=11219
theorem BSD_DegreeNonneg_p3617 : BSD_FrobeniusDegreeNonneg_OPEN 3617 := fun r => by
  have hap : (a_p 3617 : ℝ) = -57 := by exact_mod_cast BSD_ap_p3617
  have key : r ^ 2 - (a_p 3617 : ℝ) * r + ((3617 : ℕ) : ℝ) =
      (r + 57/2) ^ 2 + 11219/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (57 : ℝ)/2)]

-- p=3623: a_p=+48, 4p-a_p²=12188
theorem BSD_DegreeNonneg_p3623 : BSD_FrobeniusDegreeNonneg_OPEN 3623 := fun r => by
  have hap : (a_p 3623 : ℝ) = 48 := by exact_mod_cast BSD_ap_p3623
  have key : r ^ 2 - (a_p 3623 : ℝ) * r + ((3623 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 12188/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

-- p=3631: a_p=+48, 4p-a_p²=12220
theorem BSD_DegreeNonneg_p3631 : BSD_FrobeniusDegreeNonneg_OPEN 3631 := fun r => by
  have hap : (a_p 3631 : ℝ) = 48 := by exact_mod_cast BSD_ap_p3631
  have key : r ^ 2 - (a_p 3631 : ℝ) * r + ((3631 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 12220/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3559 : BSD_Hasse_OPEN 3559 :=
  BSD_hasse_of_degree_nonneg 3559 BSD_DegreeNonneg_p3559
theorem BSD_Hasse_OPEN_p3571 : BSD_Hasse_OPEN 3571 :=
  BSD_hasse_of_degree_nonneg 3571 BSD_DegreeNonneg_p3571
theorem BSD_Hasse_OPEN_p3581 : BSD_Hasse_OPEN 3581 :=
  BSD_hasse_of_degree_nonneg 3581 BSD_DegreeNonneg_p3581
theorem BSD_Hasse_OPEN_p3583 : BSD_Hasse_OPEN 3583 :=
  BSD_hasse_of_degree_nonneg 3583 BSD_DegreeNonneg_p3583
theorem BSD_Hasse_OPEN_p3593 : BSD_Hasse_OPEN 3593 :=
  BSD_hasse_of_degree_nonneg 3593 BSD_DegreeNonneg_p3593
theorem BSD_Hasse_OPEN_p3607 : BSD_Hasse_OPEN 3607 :=
  BSD_hasse_of_degree_nonneg 3607 BSD_DegreeNonneg_p3607
theorem BSD_Hasse_OPEN_p3613 : BSD_Hasse_OPEN 3613 :=
  BSD_hasse_of_degree_nonneg 3613 BSD_DegreeNonneg_p3613
theorem BSD_Hasse_OPEN_p3617 : BSD_Hasse_OPEN 3617 :=
  BSD_hasse_of_degree_nonneg 3617 BSD_DegreeNonneg_p3617
theorem BSD_Hasse_OPEN_p3623 : BSD_Hasse_OPEN 3623 :=
  BSD_hasse_of_degree_nonneg 3623 BSD_DegreeNonneg_p3623
theorem BSD_Hasse_OPEN_p3631 : BSD_Hasse_OPEN 3631 :=
  BSD_hasse_of_degree_nonneg 3631 BSD_DegreeNonneg_p3631

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3559 : (a_p 3559 : ℝ) ^ 2 ≤ 4 * (3559 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3559
theorem BSD_HasseBound_Disc_p3571 : (a_p 3571 : ℝ) ^ 2 ≤ 4 * (3571 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3571
theorem BSD_HasseBound_Disc_p3581 : (a_p 3581 : ℝ) ^ 2 ≤ 4 * (3581 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3581
theorem BSD_HasseBound_Disc_p3583 : (a_p 3583 : ℝ) ^ 2 ≤ 4 * (3583 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3583
theorem BSD_HasseBound_Disc_p3593 : (a_p 3593 : ℝ) ^ 2 ≤ 4 * (3593 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3593
theorem BSD_HasseBound_Disc_p3607 : (a_p 3607 : ℝ) ^ 2 ≤ 4 * (3607 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3607
theorem BSD_HasseBound_Disc_p3613 : (a_p 3613 : ℝ) ^ 2 ≤ 4 * (3613 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3613
theorem BSD_HasseBound_Disc_p3617 : (a_p 3617 : ℝ) ^ 2 ≤ 4 * (3617 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3617
theorem BSD_HasseBound_Disc_p3623 : (a_p 3623 : ℝ) ^ 2 ≤ 4 * (3623 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3623
theorem BSD_HasseBound_Disc_p3631 : (a_p 3631 : ℝ) ^ 2 ≤ 4 * (3631 : ℝ) :=
  BSD_disc_from_deg_816 BSD_DegreeNonneg_p3631

end Towers.BSD