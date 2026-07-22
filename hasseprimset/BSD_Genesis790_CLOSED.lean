/-
================================================================
Towers / BSD / BSD_Genesis790_CLOSED  (genesis-790)

HasseBridge Tier C: Hasse bounds for primes
1499..1571 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1499: card=1469, a_p=+31, disc=-5035
  p=1511: card=1471, a_p=+41, disc=-4363
  p=1523: card=1503, a_p=+21, disc=-5651
  p=1531: card=1554, a_p=-22, disc=-5640
  p=1543: card=1488, a_p=+56, disc=-3036
  p=1549: card=1595, a_p=-45, disc=-4171
  p=1553: card=1552, a_p=+2, disc=-6208
  p=1559: card=1550, a_p=+10, disc=-6136
  p=1567: card=1560, a_p=+8, disc=-6204
  p=1571: card=1572, a_p=+0, disc=-6284

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_790 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i790_p1499 : Fact (1499 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1511 : Fact (1511 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1523 : Fact (1523 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1531 : Fact (1531 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1543 : Fact (1543 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1549 : Fact (1549 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1553 : Fact (1553 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1559 : Fact (1559 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1567 : Fact (1567 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1571 : Fact (1571 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1499 : (E143_Finset 1499).card = 1469 := by native_decide
theorem BSD_E143_card_p1511 : (E143_Finset 1511).card = 1471 := by native_decide
theorem BSD_E143_card_p1523 : (E143_Finset 1523).card = 1503 := by native_decide
theorem BSD_E143_card_p1531 : (E143_Finset 1531).card = 1554 := by native_decide
theorem BSD_E143_card_p1543 : (E143_Finset 1543).card = 1488 := by native_decide
theorem BSD_E143_card_p1549 : (E143_Finset 1549).card = 1595 := by native_decide
theorem BSD_E143_card_p1553 : (E143_Finset 1553).card = 1552 := by native_decide
theorem BSD_E143_card_p1559 : (E143_Finset 1559).card = 1550 := by native_decide
theorem BSD_E143_card_p1567 : (E143_Finset 1567).card = 1560 := by native_decide
theorem BSD_E143_card_p1571 : (E143_Finset 1571).card = 1572 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1499 : a_p 1499 = (31 : ℤ) := by
  have h := BSD_E143_card_p1499; unfold a_p; omega
theorem BSD_ap_p1511 : a_p 1511 = (41 : ℤ) := by
  have h := BSD_E143_card_p1511; unfold a_p; omega
theorem BSD_ap_p1523 : a_p 1523 = (21 : ℤ) := by
  have h := BSD_E143_card_p1523; unfold a_p; omega
theorem BSD_ap_p1531 : a_p 1531 = (-22 : ℤ) := by
  have h := BSD_E143_card_p1531; unfold a_p; omega
theorem BSD_ap_p1543 : a_p 1543 = (56 : ℤ) := by
  have h := BSD_E143_card_p1543; unfold a_p; omega
theorem BSD_ap_p1549 : a_p 1549 = (-45 : ℤ) := by
  have h := BSD_E143_card_p1549; unfold a_p; omega
theorem BSD_ap_p1553 : a_p 1553 = (2 : ℤ) := by
  have h := BSD_E143_card_p1553; unfold a_p; omega
theorem BSD_ap_p1559 : a_p 1559 = (10 : ℤ) := by
  have h := BSD_E143_card_p1559; unfold a_p; omega
theorem BSD_ap_p1567 : a_p 1567 = (8 : ℤ) := by
  have h := BSD_E143_card_p1567; unfold a_p; omega
theorem BSD_ap_p1571 : a_p 1571 = (0 : ℤ) := by
  have h := BSD_E143_card_p1571; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1499: a_p=+31, 4p-a_p²=5035
theorem BSD_DegreeNonneg_p1499 : BSD_FrobeniusDegreeNonneg_OPEN 1499 := fun r => by
  have hap : (a_p 1499 : ℝ) = 31 := by exact_mod_cast BSD_ap_p1499
  have key : r ^ 2 - (a_p 1499 : ℝ) * r + ((1499 : ℕ) : ℝ) =
      (r - 31/2) ^ 2 + 5035/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (31 : ℝ)/2)]

-- p=1511: a_p=+41, 4p-a_p²=4363
theorem BSD_DegreeNonneg_p1511 : BSD_FrobeniusDegreeNonneg_OPEN 1511 := fun r => by
  have hap : (a_p 1511 : ℝ) = 41 := by exact_mod_cast BSD_ap_p1511
  have key : r ^ 2 - (a_p 1511 : ℝ) * r + ((1511 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 4363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

-- p=1523: a_p=+21, 4p-a_p²=5651
theorem BSD_DegreeNonneg_p1523 : BSD_FrobeniusDegreeNonneg_OPEN 1523 := fun r => by
  have hap : (a_p 1523 : ℝ) = 21 := by exact_mod_cast BSD_ap_p1523
  have key : r ^ 2 - (a_p 1523 : ℝ) * r + ((1523 : ℕ) : ℝ) =
      (r - 21/2) ^ 2 + 5651/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (21 : ℝ)/2)]

-- p=1531: a_p=-22, 4p-a_p²=5640
theorem BSD_DegreeNonneg_p1531 : BSD_FrobeniusDegreeNonneg_OPEN 1531 := fun r => by
  have hap : (a_p 1531 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1531
  have key : r ^ 2 - (a_p 1531 : ℝ) * r + ((1531 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 5640/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=1543: a_p=+56, 4p-a_p²=3036
theorem BSD_DegreeNonneg_p1543 : BSD_FrobeniusDegreeNonneg_OPEN 1543 := fun r => by
  have hap : (a_p 1543 : ℝ) = 56 := by exact_mod_cast BSD_ap_p1543
  have key : r ^ 2 - (a_p 1543 : ℝ) * r + ((1543 : ℕ) : ℝ) =
      (r - 56/2) ^ 2 + 3036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (56 : ℝ)/2)]

-- p=1549: a_p=-45, 4p-a_p²=4171
theorem BSD_DegreeNonneg_p1549 : BSD_FrobeniusDegreeNonneg_OPEN 1549 := fun r => by
  have hap : (a_p 1549 : ℝ) = -45 := by exact_mod_cast BSD_ap_p1549
  have key : r ^ 2 - (a_p 1549 : ℝ) * r + ((1549 : ℕ) : ℝ) =
      (r + 45/2) ^ 2 + 4171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (45 : ℝ)/2)]

-- p=1553: a_p=+2, 4p-a_p²=6208
theorem BSD_DegreeNonneg_p1553 : BSD_FrobeniusDegreeNonneg_OPEN 1553 := fun r => by
  have hap : (a_p 1553 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1553
  have key : r ^ 2 - (a_p 1553 : ℝ) * r + ((1553 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 6208/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

-- p=1559: a_p=+10, 4p-a_p²=6136
theorem BSD_DegreeNonneg_p1559 : BSD_FrobeniusDegreeNonneg_OPEN 1559 := fun r => by
  have hap : (a_p 1559 : ℝ) = 10 := by exact_mod_cast BSD_ap_p1559
  have key : r ^ 2 - (a_p 1559 : ℝ) * r + ((1559 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 6136/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

-- p=1567: a_p=+8, 4p-a_p²=6204
theorem BSD_DegreeNonneg_p1567 : BSD_FrobeniusDegreeNonneg_OPEN 1567 := fun r => by
  have hap : (a_p 1567 : ℝ) = 8 := by exact_mod_cast BSD_ap_p1567
  have key : r ^ 2 - (a_p 1567 : ℝ) * r + ((1567 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 6204/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

-- p=1571: a_p=+0, 4p-a_p²=6284
theorem BSD_DegreeNonneg_p1571 : BSD_FrobeniusDegreeNonneg_OPEN 1571 := fun r => by
  have hap : (a_p 1571 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1571
  have key : r ^ 2 - (a_p 1571 : ℝ) * r + ((1571 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 6284/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1499 : BSD_Hasse_OPEN 1499 :=
  BSD_hasse_of_degree_nonneg 1499 BSD_DegreeNonneg_p1499
theorem BSD_Hasse_OPEN_p1511 : BSD_Hasse_OPEN 1511 :=
  BSD_hasse_of_degree_nonneg 1511 BSD_DegreeNonneg_p1511
theorem BSD_Hasse_OPEN_p1523 : BSD_Hasse_OPEN 1523 :=
  BSD_hasse_of_degree_nonneg 1523 BSD_DegreeNonneg_p1523
theorem BSD_Hasse_OPEN_p1531 : BSD_Hasse_OPEN 1531 :=
  BSD_hasse_of_degree_nonneg 1531 BSD_DegreeNonneg_p1531
theorem BSD_Hasse_OPEN_p1543 : BSD_Hasse_OPEN 1543 :=
  BSD_hasse_of_degree_nonneg 1543 BSD_DegreeNonneg_p1543
theorem BSD_Hasse_OPEN_p1549 : BSD_Hasse_OPEN 1549 :=
  BSD_hasse_of_degree_nonneg 1549 BSD_DegreeNonneg_p1549
theorem BSD_Hasse_OPEN_p1553 : BSD_Hasse_OPEN 1553 :=
  BSD_hasse_of_degree_nonneg 1553 BSD_DegreeNonneg_p1553
theorem BSD_Hasse_OPEN_p1559 : BSD_Hasse_OPEN 1559 :=
  BSD_hasse_of_degree_nonneg 1559 BSD_DegreeNonneg_p1559
theorem BSD_Hasse_OPEN_p1567 : BSD_Hasse_OPEN 1567 :=
  BSD_hasse_of_degree_nonneg 1567 BSD_DegreeNonneg_p1567
theorem BSD_Hasse_OPEN_p1571 : BSD_Hasse_OPEN 1571 :=
  BSD_hasse_of_degree_nonneg 1571 BSD_DegreeNonneg_p1571

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1499 : (a_p 1499 : ℝ) ^ 2 ≤ 4 * (1499 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1499
theorem BSD_HasseBound_Disc_p1511 : (a_p 1511 : ℝ) ^ 2 ≤ 4 * (1511 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1511
theorem BSD_HasseBound_Disc_p1523 : (a_p 1523 : ℝ) ^ 2 ≤ 4 * (1523 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1523
theorem BSD_HasseBound_Disc_p1531 : (a_p 1531 : ℝ) ^ 2 ≤ 4 * (1531 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1531
theorem BSD_HasseBound_Disc_p1543 : (a_p 1543 : ℝ) ^ 2 ≤ 4 * (1543 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1543
theorem BSD_HasseBound_Disc_p1549 : (a_p 1549 : ℝ) ^ 2 ≤ 4 * (1549 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1549
theorem BSD_HasseBound_Disc_p1553 : (a_p 1553 : ℝ) ^ 2 ≤ 4 * (1553 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1553
theorem BSD_HasseBound_Disc_p1559 : (a_p 1559 : ℝ) ^ 2 ≤ 4 * (1559 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1559
theorem BSD_HasseBound_Disc_p1567 : (a_p 1567 : ℝ) ^ 2 ≤ 4 * (1567 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1567
theorem BSD_HasseBound_Disc_p1571 : (a_p 1571 : ℝ) ^ 2 ≤ 4 * (1571 : ℝ) :=
  BSD_disc_from_deg_790 BSD_DegreeNonneg_p1571

end Towers.BSD