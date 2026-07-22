/-
================================================================
Towers / BSD / BSD_Genesis815_CLOSED  (genesis-815)

HasseBridge Tier C: Hasse bounds for primes
3499..3557 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3499: card=3592, a_p=-92, disc=-5532
  p=3511: card=3544, a_p=-32, disc=-13020
  p=3517: card=3500, a_p=+18, disc=-13744
  p=3527: card=3472, a_p=+56, disc=-10972
  p=3529: card=3511, a_p=+19, disc=-13755
  p=3533: card=3570, a_p=-36, disc=-12836
  p=3539: card=3454, a_p=+86, disc=-6760
  p=3541: card=3530, a_p=+12, disc=-14020
  p=3547: card=3441, a_p=+107, disc=-2739
  p=3557: card=3499, a_p=+59, disc=-10747

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_815 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i815_p3499 : Fact (3499 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3511 : Fact (3511 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3517 : Fact (3517 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3527 : Fact (3527 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3529 : Fact (3529 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3533 : Fact (3533 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3539 : Fact (3539 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3541 : Fact (3541 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3547 : Fact (3547 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3557 : Fact (3557 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3499 : (E143_Finset 3499).card = 3592 := by native_decide
theorem BSD_E143_card_p3511 : (E143_Finset 3511).card = 3544 := by native_decide
theorem BSD_E143_card_p3517 : (E143_Finset 3517).card = 3500 := by native_decide
theorem BSD_E143_card_p3527 : (E143_Finset 3527).card = 3472 := by native_decide
theorem BSD_E143_card_p3529 : (E143_Finset 3529).card = 3511 := by native_decide
theorem BSD_E143_card_p3533 : (E143_Finset 3533).card = 3570 := by native_decide
theorem BSD_E143_card_p3539 : (E143_Finset 3539).card = 3454 := by native_decide
theorem BSD_E143_card_p3541 : (E143_Finset 3541).card = 3530 := by native_decide
theorem BSD_E143_card_p3547 : (E143_Finset 3547).card = 3441 := by native_decide
theorem BSD_E143_card_p3557 : (E143_Finset 3557).card = 3499 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3499 : a_p 3499 = (-92 : ℤ) := by
  have h := BSD_E143_card_p3499; unfold a_p; omega
theorem BSD_ap_p3511 : a_p 3511 = (-32 : ℤ) := by
  have h := BSD_E143_card_p3511; unfold a_p; omega
theorem BSD_ap_p3517 : a_p 3517 = (18 : ℤ) := by
  have h := BSD_E143_card_p3517; unfold a_p; omega
theorem BSD_ap_p3527 : a_p 3527 = (56 : ℤ) := by
  have h := BSD_E143_card_p3527; unfold a_p; omega
theorem BSD_ap_p3529 : a_p 3529 = (19 : ℤ) := by
  have h := BSD_E143_card_p3529; unfold a_p; omega
theorem BSD_ap_p3533 : a_p 3533 = (-36 : ℤ) := by
  have h := BSD_E143_card_p3533; unfold a_p; omega
theorem BSD_ap_p3539 : a_p 3539 = (86 : ℤ) := by
  have h := BSD_E143_card_p3539; unfold a_p; omega
theorem BSD_ap_p3541 : a_p 3541 = (12 : ℤ) := by
  have h := BSD_E143_card_p3541; unfold a_p; omega
theorem BSD_ap_p3547 : a_p 3547 = (107 : ℤ) := by
  have h := BSD_E143_card_p3547; unfold a_p; omega
theorem BSD_ap_p3557 : a_p 3557 = (59 : ℤ) := by
  have h := BSD_E143_card_p3557; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3499: a_p=-92, 4p-a_p²=5532
theorem BSD_DegreeNonneg_p3499 : BSD_FrobeniusDegreeNonneg_OPEN 3499 := fun r => by
  have hap : (a_p 3499 : ℝ) = -92 := by exact_mod_cast BSD_ap_p3499
  have key : r ^ 2 - (a_p 3499 : ℝ) * r + ((3499 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 5532/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

-- p=3511: a_p=-32, 4p-a_p²=13020
theorem BSD_DegreeNonneg_p3511 : BSD_FrobeniusDegreeNonneg_OPEN 3511 := fun r => by
  have hap : (a_p 3511 : ℝ) = -32 := by exact_mod_cast BSD_ap_p3511
  have key : r ^ 2 - (a_p 3511 : ℝ) * r + ((3511 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 13020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=3517: a_p=+18, 4p-a_p²=13744
theorem BSD_DegreeNonneg_p3517 : BSD_FrobeniusDegreeNonneg_OPEN 3517 := fun r => by
  have hap : (a_p 3517 : ℝ) = 18 := by exact_mod_cast BSD_ap_p3517
  have key : r ^ 2 - (a_p 3517 : ℝ) * r + ((3517 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 13744/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=3527: a_p=+56, 4p-a_p²=10972
theorem BSD_DegreeNonneg_p3527 : BSD_FrobeniusDegreeNonneg_OPEN 3527 := fun r => by
  have hap : (a_p 3527 : ℝ) = 56 := by exact_mod_cast BSD_ap_p3527
  have key : r ^ 2 - (a_p 3527 : ℝ) * r + ((3527 : ℕ) : ℝ) =
      (r - 56/2) ^ 2 + 10972/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (56 : ℝ)/2)]

-- p=3529: a_p=+19, 4p-a_p²=13755
theorem BSD_DegreeNonneg_p3529 : BSD_FrobeniusDegreeNonneg_OPEN 3529 := fun r => by
  have hap : (a_p 3529 : ℝ) = 19 := by exact_mod_cast BSD_ap_p3529
  have key : r ^ 2 - (a_p 3529 : ℝ) * r + ((3529 : ℕ) : ℝ) =
      (r - 19/2) ^ 2 + 13755/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (19 : ℝ)/2)]

-- p=3533: a_p=-36, 4p-a_p²=12836
theorem BSD_DegreeNonneg_p3533 : BSD_FrobeniusDegreeNonneg_OPEN 3533 := fun r => by
  have hap : (a_p 3533 : ℝ) = -36 := by exact_mod_cast BSD_ap_p3533
  have key : r ^ 2 - (a_p 3533 : ℝ) * r + ((3533 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 12836/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

-- p=3539: a_p=+86, 4p-a_p²=6760
theorem BSD_DegreeNonneg_p3539 : BSD_FrobeniusDegreeNonneg_OPEN 3539 := fun r => by
  have hap : (a_p 3539 : ℝ) = 86 := by exact_mod_cast BSD_ap_p3539
  have key : r ^ 2 - (a_p 3539 : ℝ) * r + ((3539 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 6760/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

-- p=3541: a_p=+12, 4p-a_p²=14020
theorem BSD_DegreeNonneg_p3541 : BSD_FrobeniusDegreeNonneg_OPEN 3541 := fun r => by
  have hap : (a_p 3541 : ℝ) = 12 := by exact_mod_cast BSD_ap_p3541
  have key : r ^ 2 - (a_p 3541 : ℝ) * r + ((3541 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 14020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=3547: a_p=+107, 4p-a_p²=2739
theorem BSD_DegreeNonneg_p3547 : BSD_FrobeniusDegreeNonneg_OPEN 3547 := fun r => by
  have hap : (a_p 3547 : ℝ) = 107 := by exact_mod_cast BSD_ap_p3547
  have key : r ^ 2 - (a_p 3547 : ℝ) * r + ((3547 : ℕ) : ℝ) =
      (r - 107/2) ^ 2 + 2739/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (107 : ℝ)/2)]

-- p=3557: a_p=+59, 4p-a_p²=10747
theorem BSD_DegreeNonneg_p3557 : BSD_FrobeniusDegreeNonneg_OPEN 3557 := fun r => by
  have hap : (a_p 3557 : ℝ) = 59 := by exact_mod_cast BSD_ap_p3557
  have key : r ^ 2 - (a_p 3557 : ℝ) * r + ((3557 : ℕ) : ℝ) =
      (r - 59/2) ^ 2 + 10747/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (59 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3499 : BSD_Hasse_OPEN 3499 :=
  BSD_hasse_of_degree_nonneg 3499 BSD_DegreeNonneg_p3499
theorem BSD_Hasse_OPEN_p3511 : BSD_Hasse_OPEN 3511 :=
  BSD_hasse_of_degree_nonneg 3511 BSD_DegreeNonneg_p3511
theorem BSD_Hasse_OPEN_p3517 : BSD_Hasse_OPEN 3517 :=
  BSD_hasse_of_degree_nonneg 3517 BSD_DegreeNonneg_p3517
theorem BSD_Hasse_OPEN_p3527 : BSD_Hasse_OPEN 3527 :=
  BSD_hasse_of_degree_nonneg 3527 BSD_DegreeNonneg_p3527
theorem BSD_Hasse_OPEN_p3529 : BSD_Hasse_OPEN 3529 :=
  BSD_hasse_of_degree_nonneg 3529 BSD_DegreeNonneg_p3529
theorem BSD_Hasse_OPEN_p3533 : BSD_Hasse_OPEN 3533 :=
  BSD_hasse_of_degree_nonneg 3533 BSD_DegreeNonneg_p3533
theorem BSD_Hasse_OPEN_p3539 : BSD_Hasse_OPEN 3539 :=
  BSD_hasse_of_degree_nonneg 3539 BSD_DegreeNonneg_p3539
theorem BSD_Hasse_OPEN_p3541 : BSD_Hasse_OPEN 3541 :=
  BSD_hasse_of_degree_nonneg 3541 BSD_DegreeNonneg_p3541
theorem BSD_Hasse_OPEN_p3547 : BSD_Hasse_OPEN 3547 :=
  BSD_hasse_of_degree_nonneg 3547 BSD_DegreeNonneg_p3547
theorem BSD_Hasse_OPEN_p3557 : BSD_Hasse_OPEN 3557 :=
  BSD_hasse_of_degree_nonneg 3557 BSD_DegreeNonneg_p3557

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3499 : (a_p 3499 : ℝ) ^ 2 ≤ 4 * (3499 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3499
theorem BSD_HasseBound_Disc_p3511 : (a_p 3511 : ℝ) ^ 2 ≤ 4 * (3511 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3511
theorem BSD_HasseBound_Disc_p3517 : (a_p 3517 : ℝ) ^ 2 ≤ 4 * (3517 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3517
theorem BSD_HasseBound_Disc_p3527 : (a_p 3527 : ℝ) ^ 2 ≤ 4 * (3527 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3527
theorem BSD_HasseBound_Disc_p3529 : (a_p 3529 : ℝ) ^ 2 ≤ 4 * (3529 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3529
theorem BSD_HasseBound_Disc_p3533 : (a_p 3533 : ℝ) ^ 2 ≤ 4 * (3533 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3533
theorem BSD_HasseBound_Disc_p3539 : (a_p 3539 : ℝ) ^ 2 ≤ 4 * (3539 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3539
theorem BSD_HasseBound_Disc_p3541 : (a_p 3541 : ℝ) ^ 2 ≤ 4 * (3541 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3541
theorem BSD_HasseBound_Disc_p3547 : (a_p 3547 : ℝ) ^ 2 ≤ 4 * (3547 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3547
theorem BSD_HasseBound_Disc_p3557 : (a_p 3557 : ℝ) ^ 2 ≤ 4 * (3557 : ℝ) :=
  BSD_disc_from_deg_815 BSD_DegreeNonneg_p3557

end Towers.BSD