/-
================================================================
Towers / BSD / BSD_Genesis817_CLOSED  (genesis-817)

HasseBridge Tier C: Hasse bounds for primes
3637..3709 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3637: card=3580, a_p=+58, disc=-11184
  p=3643: card=3718, a_p=-74, disc=-9096
  p=3659: card=3558, a_p=+102, disc=-4232
  p=3671: card=3576, a_p=+96, disc=-5468
  p=3673: card=3688, a_p=-14, disc=-14496
  p=3677: card=3684, a_p=-6, disc=-14672
  p=3691: card=3634, a_p=+58, disc=-11400
  p=3697: card=3781, a_p=-83, disc=-7899
  p=3701: card=3660, a_p=+42, disc=-13040
  p=3709: card=3748, a_p=-38, disc=-13392

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_817 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i817_p3637 : Fact (3637 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3643 : Fact (3643 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3659 : Fact (3659 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3671 : Fact (3671 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3673 : Fact (3673 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3677 : Fact (3677 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3691 : Fact (3691 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3697 : Fact (3697 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3701 : Fact (3701 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3709 : Fact (3709 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3637 : (E143_Finset 3637).card = 3580 := by native_decide
theorem BSD_E143_card_p3643 : (E143_Finset 3643).card = 3718 := by native_decide
theorem BSD_E143_card_p3659 : (E143_Finset 3659).card = 3558 := by native_decide
theorem BSD_E143_card_p3671 : (E143_Finset 3671).card = 3576 := by native_decide
theorem BSD_E143_card_p3673 : (E143_Finset 3673).card = 3688 := by native_decide
theorem BSD_E143_card_p3677 : (E143_Finset 3677).card = 3684 := by native_decide
theorem BSD_E143_card_p3691 : (E143_Finset 3691).card = 3634 := by native_decide
theorem BSD_E143_card_p3697 : (E143_Finset 3697).card = 3781 := by native_decide
theorem BSD_E143_card_p3701 : (E143_Finset 3701).card = 3660 := by native_decide
theorem BSD_E143_card_p3709 : (E143_Finset 3709).card = 3748 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3637 : a_p 3637 = (58 : ℤ) := by
  have h := BSD_E143_card_p3637; unfold a_p; omega
theorem BSD_ap_p3643 : a_p 3643 = (-74 : ℤ) := by
  have h := BSD_E143_card_p3643; unfold a_p; omega
theorem BSD_ap_p3659 : a_p 3659 = (102 : ℤ) := by
  have h := BSD_E143_card_p3659; unfold a_p; omega
theorem BSD_ap_p3671 : a_p 3671 = (96 : ℤ) := by
  have h := BSD_E143_card_p3671; unfold a_p; omega
theorem BSD_ap_p3673 : a_p 3673 = (-14 : ℤ) := by
  have h := BSD_E143_card_p3673; unfold a_p; omega
theorem BSD_ap_p3677 : a_p 3677 = (-6 : ℤ) := by
  have h := BSD_E143_card_p3677; unfold a_p; omega
theorem BSD_ap_p3691 : a_p 3691 = (58 : ℤ) := by
  have h := BSD_E143_card_p3691; unfold a_p; omega
theorem BSD_ap_p3697 : a_p 3697 = (-83 : ℤ) := by
  have h := BSD_E143_card_p3697; unfold a_p; omega
theorem BSD_ap_p3701 : a_p 3701 = (42 : ℤ) := by
  have h := BSD_E143_card_p3701; unfold a_p; omega
theorem BSD_ap_p3709 : a_p 3709 = (-38 : ℤ) := by
  have h := BSD_E143_card_p3709; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3637: a_p=+58, 4p-a_p²=11184
theorem BSD_DegreeNonneg_p3637 : BSD_FrobeniusDegreeNonneg_OPEN 3637 := fun r => by
  have hap : (a_p 3637 : ℝ) = 58 := by exact_mod_cast BSD_ap_p3637
  have key : r ^ 2 - (a_p 3637 : ℝ) * r + ((3637 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 11184/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

-- p=3643: a_p=-74, 4p-a_p²=9096
theorem BSD_DegreeNonneg_p3643 : BSD_FrobeniusDegreeNonneg_OPEN 3643 := fun r => by
  have hap : (a_p 3643 : ℝ) = -74 := by exact_mod_cast BSD_ap_p3643
  have key : r ^ 2 - (a_p 3643 : ℝ) * r + ((3643 : ℕ) : ℝ) =
      (r + 74/2) ^ 2 + 9096/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (74 : ℝ)/2)]

-- p=3659: a_p=+102, 4p-a_p²=4232
theorem BSD_DegreeNonneg_p3659 : BSD_FrobeniusDegreeNonneg_OPEN 3659 := fun r => by
  have hap : (a_p 3659 : ℝ) = 102 := by exact_mod_cast BSD_ap_p3659
  have key : r ^ 2 - (a_p 3659 : ℝ) * r + ((3659 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 4232/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

-- p=3671: a_p=+96, 4p-a_p²=5468
theorem BSD_DegreeNonneg_p3671 : BSD_FrobeniusDegreeNonneg_OPEN 3671 := fun r => by
  have hap : (a_p 3671 : ℝ) = 96 := by exact_mod_cast BSD_ap_p3671
  have key : r ^ 2 - (a_p 3671 : ℝ) * r + ((3671 : ℕ) : ℝ) =
      (r - 96/2) ^ 2 + 5468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (96 : ℝ)/2)]

-- p=3673: a_p=-14, 4p-a_p²=14496
theorem BSD_DegreeNonneg_p3673 : BSD_FrobeniusDegreeNonneg_OPEN 3673 := fun r => by
  have hap : (a_p 3673 : ℝ) = -14 := by exact_mod_cast BSD_ap_p3673
  have key : r ^ 2 - (a_p 3673 : ℝ) * r + ((3673 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 14496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

-- p=3677: a_p=-6, 4p-a_p²=14672
theorem BSD_DegreeNonneg_p3677 : BSD_FrobeniusDegreeNonneg_OPEN 3677 := fun r => by
  have hap : (a_p 3677 : ℝ) = -6 := by exact_mod_cast BSD_ap_p3677
  have key : r ^ 2 - (a_p 3677 : ℝ) * r + ((3677 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 14672/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

-- p=3691: a_p=+58, 4p-a_p²=11400
theorem BSD_DegreeNonneg_p3691 : BSD_FrobeniusDegreeNonneg_OPEN 3691 := fun r => by
  have hap : (a_p 3691 : ℝ) = 58 := by exact_mod_cast BSD_ap_p3691
  have key : r ^ 2 - (a_p 3691 : ℝ) * r + ((3691 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 11400/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

-- p=3697: a_p=-83, 4p-a_p²=7899
theorem BSD_DegreeNonneg_p3697 : BSD_FrobeniusDegreeNonneg_OPEN 3697 := fun r => by
  have hap : (a_p 3697 : ℝ) = -83 := by exact_mod_cast BSD_ap_p3697
  have key : r ^ 2 - (a_p 3697 : ℝ) * r + ((3697 : ℕ) : ℝ) =
      (r + 83/2) ^ 2 + 7899/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (83 : ℝ)/2)]

-- p=3701: a_p=+42, 4p-a_p²=13040
theorem BSD_DegreeNonneg_p3701 : BSD_FrobeniusDegreeNonneg_OPEN 3701 := fun r => by
  have hap : (a_p 3701 : ℝ) = 42 := by exact_mod_cast BSD_ap_p3701
  have key : r ^ 2 - (a_p 3701 : ℝ) * r + ((3701 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 13040/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

-- p=3709: a_p=-38, 4p-a_p²=13392
theorem BSD_DegreeNonneg_p3709 : BSD_FrobeniusDegreeNonneg_OPEN 3709 := fun r => by
  have hap : (a_p 3709 : ℝ) = -38 := by exact_mod_cast BSD_ap_p3709
  have key : r ^ 2 - (a_p 3709 : ℝ) * r + ((3709 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 13392/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3637 : BSD_Hasse_OPEN 3637 :=
  BSD_hasse_of_degree_nonneg 3637 BSD_DegreeNonneg_p3637
theorem BSD_Hasse_OPEN_p3643 : BSD_Hasse_OPEN 3643 :=
  BSD_hasse_of_degree_nonneg 3643 BSD_DegreeNonneg_p3643
theorem BSD_Hasse_OPEN_p3659 : BSD_Hasse_OPEN 3659 :=
  BSD_hasse_of_degree_nonneg 3659 BSD_DegreeNonneg_p3659
theorem BSD_Hasse_OPEN_p3671 : BSD_Hasse_OPEN 3671 :=
  BSD_hasse_of_degree_nonneg 3671 BSD_DegreeNonneg_p3671
theorem BSD_Hasse_OPEN_p3673 : BSD_Hasse_OPEN 3673 :=
  BSD_hasse_of_degree_nonneg 3673 BSD_DegreeNonneg_p3673
theorem BSD_Hasse_OPEN_p3677 : BSD_Hasse_OPEN 3677 :=
  BSD_hasse_of_degree_nonneg 3677 BSD_DegreeNonneg_p3677
theorem BSD_Hasse_OPEN_p3691 : BSD_Hasse_OPEN 3691 :=
  BSD_hasse_of_degree_nonneg 3691 BSD_DegreeNonneg_p3691
theorem BSD_Hasse_OPEN_p3697 : BSD_Hasse_OPEN 3697 :=
  BSD_hasse_of_degree_nonneg 3697 BSD_DegreeNonneg_p3697
theorem BSD_Hasse_OPEN_p3701 : BSD_Hasse_OPEN 3701 :=
  BSD_hasse_of_degree_nonneg 3701 BSD_DegreeNonneg_p3701
theorem BSD_Hasse_OPEN_p3709 : BSD_Hasse_OPEN 3709 :=
  BSD_hasse_of_degree_nonneg 3709 BSD_DegreeNonneg_p3709

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3637 : (a_p 3637 : ℝ) ^ 2 ≤ 4 * (3637 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3637
theorem BSD_HasseBound_Disc_p3643 : (a_p 3643 : ℝ) ^ 2 ≤ 4 * (3643 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3643
theorem BSD_HasseBound_Disc_p3659 : (a_p 3659 : ℝ) ^ 2 ≤ 4 * (3659 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3659
theorem BSD_HasseBound_Disc_p3671 : (a_p 3671 : ℝ) ^ 2 ≤ 4 * (3671 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3671
theorem BSD_HasseBound_Disc_p3673 : (a_p 3673 : ℝ) ^ 2 ≤ 4 * (3673 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3673
theorem BSD_HasseBound_Disc_p3677 : (a_p 3677 : ℝ) ^ 2 ≤ 4 * (3677 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3677
theorem BSD_HasseBound_Disc_p3691 : (a_p 3691 : ℝ) ^ 2 ≤ 4 * (3691 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3691
theorem BSD_HasseBound_Disc_p3697 : (a_p 3697 : ℝ) ^ 2 ≤ 4 * (3697 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3697
theorem BSD_HasseBound_Disc_p3701 : (a_p 3701 : ℝ) ^ 2 ≤ 4 * (3701 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3701
theorem BSD_HasseBound_Disc_p3709 : (a_p 3709 : ℝ) ^ 2 ≤ 4 * (3709 : ℝ) :=
  BSD_disc_from_deg_817 BSD_DegreeNonneg_p3709

end Towers.BSD