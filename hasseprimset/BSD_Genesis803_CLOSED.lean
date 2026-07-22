/-
================================================================
Towers / BSD / BSD_Genesis803_CLOSED  (genesis-803)

HasseBridge Tier C: Hasse bounds for primes
2521..2593 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2521: card=2572, a_p=-50, disc=-7584
  p=2531: card=2535, a_p=-3, disc=-10115
  p=2539: card=2544, a_p=-4, disc=-10140
  p=2543: card=2528, a_p=+16, disc=-9916
  p=2549: card=2526, a_p=+24, disc=-9620
  p=2551: card=2568, a_p=-16, disc=-9948
  p=2557: card=2569, a_p=-11, disc=-10107
  p=2579: card=2672, a_p=-92, disc=-1852
  p=2591: card=2648, a_p=-56, disc=-7228
  p=2593: card=2662, a_p=-68, disc=-5748

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_803 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i803_p2521 : Fact (2521 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2531 : Fact (2531 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2539 : Fact (2539 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2543 : Fact (2543 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2549 : Fact (2549 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2551 : Fact (2551 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2557 : Fact (2557 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2579 : Fact (2579 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2591 : Fact (2591 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2593 : Fact (2593 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2521 : (E143_Finset 2521).card = 2572 := by native_decide
theorem BSD_E143_card_p2531 : (E143_Finset 2531).card = 2535 := by native_decide
theorem BSD_E143_card_p2539 : (E143_Finset 2539).card = 2544 := by native_decide
theorem BSD_E143_card_p2543 : (E143_Finset 2543).card = 2528 := by native_decide
theorem BSD_E143_card_p2549 : (E143_Finset 2549).card = 2526 := by native_decide
theorem BSD_E143_card_p2551 : (E143_Finset 2551).card = 2568 := by native_decide
theorem BSD_E143_card_p2557 : (E143_Finset 2557).card = 2569 := by native_decide
theorem BSD_E143_card_p2579 : (E143_Finset 2579).card = 2672 := by native_decide
theorem BSD_E143_card_p2591 : (E143_Finset 2591).card = 2648 := by native_decide
theorem BSD_E143_card_p2593 : (E143_Finset 2593).card = 2662 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2521 : a_p 2521 = (-50 : ℤ) := by
  have h := BSD_E143_card_p2521; unfold a_p; omega
theorem BSD_ap_p2531 : a_p 2531 = (-3 : ℤ) := by
  have h := BSD_E143_card_p2531; unfold a_p; omega
theorem BSD_ap_p2539 : a_p 2539 = (-4 : ℤ) := by
  have h := BSD_E143_card_p2539; unfold a_p; omega
theorem BSD_ap_p2543 : a_p 2543 = (16 : ℤ) := by
  have h := BSD_E143_card_p2543; unfold a_p; omega
theorem BSD_ap_p2549 : a_p 2549 = (24 : ℤ) := by
  have h := BSD_E143_card_p2549; unfold a_p; omega
theorem BSD_ap_p2551 : a_p 2551 = (-16 : ℤ) := by
  have h := BSD_E143_card_p2551; unfold a_p; omega
theorem BSD_ap_p2557 : a_p 2557 = (-11 : ℤ) := by
  have h := BSD_E143_card_p2557; unfold a_p; omega
theorem BSD_ap_p2579 : a_p 2579 = (-92 : ℤ) := by
  have h := BSD_E143_card_p2579; unfold a_p; omega
theorem BSD_ap_p2591 : a_p 2591 = (-56 : ℤ) := by
  have h := BSD_E143_card_p2591; unfold a_p; omega
theorem BSD_ap_p2593 : a_p 2593 = (-68 : ℤ) := by
  have h := BSD_E143_card_p2593; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2521: a_p=-50, 4p-a_p²=7584
theorem BSD_DegreeNonneg_p2521 : BSD_FrobeniusDegreeNonneg_OPEN 2521 := fun r => by
  have hap : (a_p 2521 : ℝ) = -50 := by exact_mod_cast BSD_ap_p2521
  have key : r ^ 2 - (a_p 2521 : ℝ) * r + ((2521 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 7584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

-- p=2531: a_p=-3, 4p-a_p²=10115
theorem BSD_DegreeNonneg_p2531 : BSD_FrobeniusDegreeNonneg_OPEN 2531 := fun r => by
  have hap : (a_p 2531 : ℝ) = -3 := by exact_mod_cast BSD_ap_p2531
  have key : r ^ 2 - (a_p 2531 : ℝ) * r + ((2531 : ℕ) : ℝ) =
      (r + 3/2) ^ 2 + 10115/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (3 : ℝ)/2)]

-- p=2539: a_p=-4, 4p-a_p²=10140
theorem BSD_DegreeNonneg_p2539 : BSD_FrobeniusDegreeNonneg_OPEN 2539 := fun r => by
  have hap : (a_p 2539 : ℝ) = -4 := by exact_mod_cast BSD_ap_p2539
  have key : r ^ 2 - (a_p 2539 : ℝ) * r + ((2539 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 10140/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

-- p=2543: a_p=+16, 4p-a_p²=9916
theorem BSD_DegreeNonneg_p2543 : BSD_FrobeniusDegreeNonneg_OPEN 2543 := fun r => by
  have hap : (a_p 2543 : ℝ) = 16 := by exact_mod_cast BSD_ap_p2543
  have key : r ^ 2 - (a_p 2543 : ℝ) * r + ((2543 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 9916/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

-- p=2549: a_p=+24, 4p-a_p²=9620
theorem BSD_DegreeNonneg_p2549 : BSD_FrobeniusDegreeNonneg_OPEN 2549 := fun r => by
  have hap : (a_p 2549 : ℝ) = 24 := by exact_mod_cast BSD_ap_p2549
  have key : r ^ 2 - (a_p 2549 : ℝ) * r + ((2549 : ℕ) : ℝ) =
      (r - 24/2) ^ 2 + 9620/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (24 : ℝ)/2)]

-- p=2551: a_p=-16, 4p-a_p²=9948
theorem BSD_DegreeNonneg_p2551 : BSD_FrobeniusDegreeNonneg_OPEN 2551 := fun r => by
  have hap : (a_p 2551 : ℝ) = -16 := by exact_mod_cast BSD_ap_p2551
  have key : r ^ 2 - (a_p 2551 : ℝ) * r + ((2551 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 9948/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

-- p=2557: a_p=-11, 4p-a_p²=10107
theorem BSD_DegreeNonneg_p2557 : BSD_FrobeniusDegreeNonneg_OPEN 2557 := fun r => by
  have hap : (a_p 2557 : ℝ) = -11 := by exact_mod_cast BSD_ap_p2557
  have key : r ^ 2 - (a_p 2557 : ℝ) * r + ((2557 : ℕ) : ℝ) =
      (r + 11/2) ^ 2 + 10107/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (11 : ℝ)/2)]

-- p=2579: a_p=-92, 4p-a_p²=1852
theorem BSD_DegreeNonneg_p2579 : BSD_FrobeniusDegreeNonneg_OPEN 2579 := fun r => by
  have hap : (a_p 2579 : ℝ) = -92 := by exact_mod_cast BSD_ap_p2579
  have key : r ^ 2 - (a_p 2579 : ℝ) * r + ((2579 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 1852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

-- p=2591: a_p=-56, 4p-a_p²=7228
theorem BSD_DegreeNonneg_p2591 : BSD_FrobeniusDegreeNonneg_OPEN 2591 := fun r => by
  have hap : (a_p 2591 : ℝ) = -56 := by exact_mod_cast BSD_ap_p2591
  have key : r ^ 2 - (a_p 2591 : ℝ) * r + ((2591 : ℕ) : ℝ) =
      (r + 56/2) ^ 2 + 7228/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (56 : ℝ)/2)]

-- p=2593: a_p=-68, 4p-a_p²=5748
theorem BSD_DegreeNonneg_p2593 : BSD_FrobeniusDegreeNonneg_OPEN 2593 := fun r => by
  have hap : (a_p 2593 : ℝ) = -68 := by exact_mod_cast BSD_ap_p2593
  have key : r ^ 2 - (a_p 2593 : ℝ) * r + ((2593 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 5748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2521 : BSD_Hasse_OPEN 2521 :=
  BSD_hasse_of_degree_nonneg 2521 BSD_DegreeNonneg_p2521
theorem BSD_Hasse_OPEN_p2531 : BSD_Hasse_OPEN 2531 :=
  BSD_hasse_of_degree_nonneg 2531 BSD_DegreeNonneg_p2531
theorem BSD_Hasse_OPEN_p2539 : BSD_Hasse_OPEN 2539 :=
  BSD_hasse_of_degree_nonneg 2539 BSD_DegreeNonneg_p2539
theorem BSD_Hasse_OPEN_p2543 : BSD_Hasse_OPEN 2543 :=
  BSD_hasse_of_degree_nonneg 2543 BSD_DegreeNonneg_p2543
theorem BSD_Hasse_OPEN_p2549 : BSD_Hasse_OPEN 2549 :=
  BSD_hasse_of_degree_nonneg 2549 BSD_DegreeNonneg_p2549
theorem BSD_Hasse_OPEN_p2551 : BSD_Hasse_OPEN 2551 :=
  BSD_hasse_of_degree_nonneg 2551 BSD_DegreeNonneg_p2551
theorem BSD_Hasse_OPEN_p2557 : BSD_Hasse_OPEN 2557 :=
  BSD_hasse_of_degree_nonneg 2557 BSD_DegreeNonneg_p2557
theorem BSD_Hasse_OPEN_p2579 : BSD_Hasse_OPEN 2579 :=
  BSD_hasse_of_degree_nonneg 2579 BSD_DegreeNonneg_p2579
theorem BSD_Hasse_OPEN_p2591 : BSD_Hasse_OPEN 2591 :=
  BSD_hasse_of_degree_nonneg 2591 BSD_DegreeNonneg_p2591
theorem BSD_Hasse_OPEN_p2593 : BSD_Hasse_OPEN 2593 :=
  BSD_hasse_of_degree_nonneg 2593 BSD_DegreeNonneg_p2593

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2521 : (a_p 2521 : ℝ) ^ 2 ≤ 4 * (2521 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2521
theorem BSD_HasseBound_Disc_p2531 : (a_p 2531 : ℝ) ^ 2 ≤ 4 * (2531 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2531
theorem BSD_HasseBound_Disc_p2539 : (a_p 2539 : ℝ) ^ 2 ≤ 4 * (2539 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2539
theorem BSD_HasseBound_Disc_p2543 : (a_p 2543 : ℝ) ^ 2 ≤ 4 * (2543 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2543
theorem BSD_HasseBound_Disc_p2549 : (a_p 2549 : ℝ) ^ 2 ≤ 4 * (2549 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2549
theorem BSD_HasseBound_Disc_p2551 : (a_p 2551 : ℝ) ^ 2 ≤ 4 * (2551 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2551
theorem BSD_HasseBound_Disc_p2557 : (a_p 2557 : ℝ) ^ 2 ≤ 4 * (2557 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2557
theorem BSD_HasseBound_Disc_p2579 : (a_p 2579 : ℝ) ^ 2 ≤ 4 * (2579 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2579
theorem BSD_HasseBound_Disc_p2591 : (a_p 2591 : ℝ) ^ 2 ≤ 4 * (2591 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2591
theorem BSD_HasseBound_Disc_p2593 : (a_p 2593 : ℝ) ^ 2 ≤ 4 * (2593 : ℝ) :=
  BSD_disc_from_deg_803 BSD_DegreeNonneg_p2593

end Towers.BSD