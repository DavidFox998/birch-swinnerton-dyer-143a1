/-
================================================================
Towers / BSD / BSD_Genesis851_CLOSED  (genesis-851)

HasseBridge Tier C: Hasse bounds for primes
6569..6659 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6569: card=6552, a_p=+18, disc=-25952
  p=6571: card=6552, a_p=+20, disc=-25884
  p=6577: card=6660, a_p=-82, disc=-19584
  p=6581: card=6711, a_p=-129, disc=-9683
  p=6599: card=6638, a_p=-38, disc=-24952
  p=6607: card=6510, a_p=+98, disc=-16824
  p=6619: card=6730, a_p=-110, disc=-14376
  p=6637: card=6756, a_p=-118, disc=-12624
  p=6653: card=6589, a_p=+65, disc=-22387
  p=6659: card=6591, a_p=+69, disc=-21875

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_851 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i851_p6569 : Fact (6569 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6571 : Fact (6571 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6577 : Fact (6577 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6581 : Fact (6581 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6599 : Fact (6599 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6607 : Fact (6607 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6619 : Fact (6619 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6637 : Fact (6637 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6653 : Fact (6653 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6659 : Fact (6659 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6569 : (E143_Finset 6569).card = 6552 := by native_decide
theorem BSD_E143_card_p6571 : (E143_Finset 6571).card = 6552 := by native_decide
theorem BSD_E143_card_p6577 : (E143_Finset 6577).card = 6660 := by native_decide
theorem BSD_E143_card_p6581 : (E143_Finset 6581).card = 6711 := by native_decide
theorem BSD_E143_card_p6599 : (E143_Finset 6599).card = 6638 := by native_decide
theorem BSD_E143_card_p6607 : (E143_Finset 6607).card = 6510 := by native_decide
theorem BSD_E143_card_p6619 : (E143_Finset 6619).card = 6730 := by native_decide
theorem BSD_E143_card_p6637 : (E143_Finset 6637).card = 6756 := by native_decide
theorem BSD_E143_card_p6653 : (E143_Finset 6653).card = 6589 := by native_decide
theorem BSD_E143_card_p6659 : (E143_Finset 6659).card = 6591 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6569 : a_p 6569 = (18 : ℤ) := by
  have h := BSD_E143_card_p6569; unfold a_p; omega
theorem BSD_ap_p6571 : a_p 6571 = (20 : ℤ) := by
  have h := BSD_E143_card_p6571; unfold a_p; omega
theorem BSD_ap_p6577 : a_p 6577 = (-82 : ℤ) := by
  have h := BSD_E143_card_p6577; unfold a_p; omega
theorem BSD_ap_p6581 : a_p 6581 = (-129 : ℤ) := by
  have h := BSD_E143_card_p6581; unfold a_p; omega
theorem BSD_ap_p6599 : a_p 6599 = (-38 : ℤ) := by
  have h := BSD_E143_card_p6599; unfold a_p; omega
theorem BSD_ap_p6607 : a_p 6607 = (98 : ℤ) := by
  have h := BSD_E143_card_p6607; unfold a_p; omega
theorem BSD_ap_p6619 : a_p 6619 = (-110 : ℤ) := by
  have h := BSD_E143_card_p6619; unfold a_p; omega
theorem BSD_ap_p6637 : a_p 6637 = (-118 : ℤ) := by
  have h := BSD_E143_card_p6637; unfold a_p; omega
theorem BSD_ap_p6653 : a_p 6653 = (65 : ℤ) := by
  have h := BSD_E143_card_p6653; unfold a_p; omega
theorem BSD_ap_p6659 : a_p 6659 = (69 : ℤ) := by
  have h := BSD_E143_card_p6659; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6569: a_p=+18, 4p-a_p²=25952
theorem BSD_DegreeNonneg_p6569 : BSD_FrobeniusDegreeNonneg_OPEN 6569 := fun r => by
  have hap : (a_p 6569 : ℝ) = 18 := by exact_mod_cast BSD_ap_p6569
  have key : r ^ 2 - (a_p 6569 : ℝ) * r + ((6569 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 25952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=6571: a_p=+20, 4p-a_p²=25884
theorem BSD_DegreeNonneg_p6571 : BSD_FrobeniusDegreeNonneg_OPEN 6571 := fun r => by
  have hap : (a_p 6571 : ℝ) = 20 := by exact_mod_cast BSD_ap_p6571
  have key : r ^ 2 - (a_p 6571 : ℝ) * r + ((6571 : ℕ) : ℝ) =
      (r - 20/2) ^ 2 + 25884/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (20 : ℝ)/2)]

-- p=6577: a_p=-82, 4p-a_p²=19584
theorem BSD_DegreeNonneg_p6577 : BSD_FrobeniusDegreeNonneg_OPEN 6577 := fun r => by
  have hap : (a_p 6577 : ℝ) = -82 := by exact_mod_cast BSD_ap_p6577
  have key : r ^ 2 - (a_p 6577 : ℝ) * r + ((6577 : ℕ) : ℝ) =
      (r + 82/2) ^ 2 + 19584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (82 : ℝ)/2)]

-- p=6581: a_p=-129, 4p-a_p²=9683
theorem BSD_DegreeNonneg_p6581 : BSD_FrobeniusDegreeNonneg_OPEN 6581 := fun r => by
  have hap : (a_p 6581 : ℝ) = -129 := by exact_mod_cast BSD_ap_p6581
  have key : r ^ 2 - (a_p 6581 : ℝ) * r + ((6581 : ℕ) : ℝ) =
      (r + 129/2) ^ 2 + 9683/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (129 : ℝ)/2)]

-- p=6599: a_p=-38, 4p-a_p²=24952
theorem BSD_DegreeNonneg_p6599 : BSD_FrobeniusDegreeNonneg_OPEN 6599 := fun r => by
  have hap : (a_p 6599 : ℝ) = -38 := by exact_mod_cast BSD_ap_p6599
  have key : r ^ 2 - (a_p 6599 : ℝ) * r + ((6599 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 24952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

-- p=6607: a_p=+98, 4p-a_p²=16824
theorem BSD_DegreeNonneg_p6607 : BSD_FrobeniusDegreeNonneg_OPEN 6607 := fun r => by
  have hap : (a_p 6607 : ℝ) = 98 := by exact_mod_cast BSD_ap_p6607
  have key : r ^ 2 - (a_p 6607 : ℝ) * r + ((6607 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 16824/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

-- p=6619: a_p=-110, 4p-a_p²=14376
theorem BSD_DegreeNonneg_p6619 : BSD_FrobeniusDegreeNonneg_OPEN 6619 := fun r => by
  have hap : (a_p 6619 : ℝ) = -110 := by exact_mod_cast BSD_ap_p6619
  have key : r ^ 2 - (a_p 6619 : ℝ) * r + ((6619 : ℕ) : ℝ) =
      (r + 110/2) ^ 2 + 14376/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (110 : ℝ)/2)]

-- p=6637: a_p=-118, 4p-a_p²=12624
theorem BSD_DegreeNonneg_p6637 : BSD_FrobeniusDegreeNonneg_OPEN 6637 := fun r => by
  have hap : (a_p 6637 : ℝ) = -118 := by exact_mod_cast BSD_ap_p6637
  have key : r ^ 2 - (a_p 6637 : ℝ) * r + ((6637 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 12624/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

-- p=6653: a_p=+65, 4p-a_p²=22387
theorem BSD_DegreeNonneg_p6653 : BSD_FrobeniusDegreeNonneg_OPEN 6653 := fun r => by
  have hap : (a_p 6653 : ℝ) = 65 := by exact_mod_cast BSD_ap_p6653
  have key : r ^ 2 - (a_p 6653 : ℝ) * r + ((6653 : ℕ) : ℝ) =
      (r - 65/2) ^ 2 + 22387/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (65 : ℝ)/2)]

-- p=6659: a_p=+69, 4p-a_p²=21875
theorem BSD_DegreeNonneg_p6659 : BSD_FrobeniusDegreeNonneg_OPEN 6659 := fun r => by
  have hap : (a_p 6659 : ℝ) = 69 := by exact_mod_cast BSD_ap_p6659
  have key : r ^ 2 - (a_p 6659 : ℝ) * r + ((6659 : ℕ) : ℝ) =
      (r - 69/2) ^ 2 + 21875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (69 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6569 : BSD_Hasse_OPEN 6569 :=
  BSD_hasse_of_degree_nonneg 6569 BSD_DegreeNonneg_p6569
theorem BSD_Hasse_OPEN_p6571 : BSD_Hasse_OPEN 6571 :=
  BSD_hasse_of_degree_nonneg 6571 BSD_DegreeNonneg_p6571
theorem BSD_Hasse_OPEN_p6577 : BSD_Hasse_OPEN 6577 :=
  BSD_hasse_of_degree_nonneg 6577 BSD_DegreeNonneg_p6577
theorem BSD_Hasse_OPEN_p6581 : BSD_Hasse_OPEN 6581 :=
  BSD_hasse_of_degree_nonneg 6581 BSD_DegreeNonneg_p6581
theorem BSD_Hasse_OPEN_p6599 : BSD_Hasse_OPEN 6599 :=
  BSD_hasse_of_degree_nonneg 6599 BSD_DegreeNonneg_p6599
theorem BSD_Hasse_OPEN_p6607 : BSD_Hasse_OPEN 6607 :=
  BSD_hasse_of_degree_nonneg 6607 BSD_DegreeNonneg_p6607
theorem BSD_Hasse_OPEN_p6619 : BSD_Hasse_OPEN 6619 :=
  BSD_hasse_of_degree_nonneg 6619 BSD_DegreeNonneg_p6619
theorem BSD_Hasse_OPEN_p6637 : BSD_Hasse_OPEN 6637 :=
  BSD_hasse_of_degree_nonneg 6637 BSD_DegreeNonneg_p6637
theorem BSD_Hasse_OPEN_p6653 : BSD_Hasse_OPEN 6653 :=
  BSD_hasse_of_degree_nonneg 6653 BSD_DegreeNonneg_p6653
theorem BSD_Hasse_OPEN_p6659 : BSD_Hasse_OPEN 6659 :=
  BSD_hasse_of_degree_nonneg 6659 BSD_DegreeNonneg_p6659

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6569 : (a_p 6569 : ℝ) ^ 2 ≤ 4 * (6569 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6569
theorem BSD_HasseBound_Disc_p6571 : (a_p 6571 : ℝ) ^ 2 ≤ 4 * (6571 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6571
theorem BSD_HasseBound_Disc_p6577 : (a_p 6577 : ℝ) ^ 2 ≤ 4 * (6577 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6577
theorem BSD_HasseBound_Disc_p6581 : (a_p 6581 : ℝ) ^ 2 ≤ 4 * (6581 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6581
theorem BSD_HasseBound_Disc_p6599 : (a_p 6599 : ℝ) ^ 2 ≤ 4 * (6599 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6599
theorem BSD_HasseBound_Disc_p6607 : (a_p 6607 : ℝ) ^ 2 ≤ 4 * (6607 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6607
theorem BSD_HasseBound_Disc_p6619 : (a_p 6619 : ℝ) ^ 2 ≤ 4 * (6619 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6619
theorem BSD_HasseBound_Disc_p6637 : (a_p 6637 : ℝ) ^ 2 ≤ 4 * (6637 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6637
theorem BSD_HasseBound_Disc_p6653 : (a_p 6653 : ℝ) ^ 2 ≤ 4 * (6653 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6653
theorem BSD_HasseBound_Disc_p6659 : (a_p 6659 : ℝ) ^ 2 ≤ 4 * (6659 : ℝ) :=
  BSD_disc_from_deg_851 BSD_DegreeNonneg_p6659

end Towers.BSD