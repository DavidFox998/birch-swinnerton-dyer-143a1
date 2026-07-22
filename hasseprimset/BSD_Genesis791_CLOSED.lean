/-
================================================================
Towers / BSD / BSD_Genesis791_CLOSED  (genesis-791)

HasseBridge Tier C: Hasse bounds for primes
1579..1627 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1579: card=1576, a_p=+4, disc=-6300
  p=1583: card=1606, a_p=-22, disc=-5848
  p=1597: card=1562, a_p=+36, disc=-5092
  p=1601: card=1556, a_p=+46, disc=-4288
  p=1607: card=1649, a_p=-41, disc=-4747
  p=1609: card=1612, a_p=-2, disc=-6432
  p=1613: card=1634, a_p=-20, disc=-6052
  p=1619: card=1660, a_p=-40, disc=-4876
  p=1621: card=1632, a_p=-10, disc=-6384
  p=1627: card=1636, a_p=-8, disc=-6444

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_791 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i791_p1579 : Fact (1579 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1583 : Fact (1583 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1597 : Fact (1597 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1601 : Fact (1601 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1607 : Fact (1607 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1609 : Fact (1609 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1613 : Fact (1613 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1619 : Fact (1619 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1621 : Fact (1621 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1627 : Fact (1627 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1579 : (E143_Finset 1579).card = 1576 := by native_decide
theorem BSD_E143_card_p1583 : (E143_Finset 1583).card = 1606 := by native_decide
theorem BSD_E143_card_p1597 : (E143_Finset 1597).card = 1562 := by native_decide
theorem BSD_E143_card_p1601 : (E143_Finset 1601).card = 1556 := by native_decide
theorem BSD_E143_card_p1607 : (E143_Finset 1607).card = 1649 := by native_decide
theorem BSD_E143_card_p1609 : (E143_Finset 1609).card = 1612 := by native_decide
theorem BSD_E143_card_p1613 : (E143_Finset 1613).card = 1634 := by native_decide
theorem BSD_E143_card_p1619 : (E143_Finset 1619).card = 1660 := by native_decide
theorem BSD_E143_card_p1621 : (E143_Finset 1621).card = 1632 := by native_decide
theorem BSD_E143_card_p1627 : (E143_Finset 1627).card = 1636 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1579 : a_p 1579 = (4 : ℤ) := by
  have h := BSD_E143_card_p1579; unfold a_p; omega
theorem BSD_ap_p1583 : a_p 1583 = (-22 : ℤ) := by
  have h := BSD_E143_card_p1583; unfold a_p; omega
theorem BSD_ap_p1597 : a_p 1597 = (36 : ℤ) := by
  have h := BSD_E143_card_p1597; unfold a_p; omega
theorem BSD_ap_p1601 : a_p 1601 = (46 : ℤ) := by
  have h := BSD_E143_card_p1601; unfold a_p; omega
theorem BSD_ap_p1607 : a_p 1607 = (-41 : ℤ) := by
  have h := BSD_E143_card_p1607; unfold a_p; omega
theorem BSD_ap_p1609 : a_p 1609 = (-2 : ℤ) := by
  have h := BSD_E143_card_p1609; unfold a_p; omega
theorem BSD_ap_p1613 : a_p 1613 = (-20 : ℤ) := by
  have h := BSD_E143_card_p1613; unfold a_p; omega
theorem BSD_ap_p1619 : a_p 1619 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1619; unfold a_p; omega
theorem BSD_ap_p1621 : a_p 1621 = (-10 : ℤ) := by
  have h := BSD_E143_card_p1621; unfold a_p; omega
theorem BSD_ap_p1627 : a_p 1627 = (-8 : ℤ) := by
  have h := BSD_E143_card_p1627; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1579: a_p=+4, 4p-a_p²=6300
theorem BSD_DegreeNonneg_p1579 : BSD_FrobeniusDegreeNonneg_OPEN 1579 := fun r => by
  have hap : (a_p 1579 : ℝ) = 4 := by exact_mod_cast BSD_ap_p1579
  have key : r ^ 2 - (a_p 1579 : ℝ) * r + ((1579 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 6300/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

-- p=1583: a_p=-22, 4p-a_p²=5848
theorem BSD_DegreeNonneg_p1583 : BSD_FrobeniusDegreeNonneg_OPEN 1583 := fun r => by
  have hap : (a_p 1583 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1583
  have key : r ^ 2 - (a_p 1583 : ℝ) * r + ((1583 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 5848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=1597: a_p=+36, 4p-a_p²=5092
theorem BSD_DegreeNonneg_p1597 : BSD_FrobeniusDegreeNonneg_OPEN 1597 := fun r => by
  have hap : (a_p 1597 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1597
  have key : r ^ 2 - (a_p 1597 : ℝ) * r + ((1597 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 5092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

-- p=1601: a_p=+46, 4p-a_p²=4288
theorem BSD_DegreeNonneg_p1601 : BSD_FrobeniusDegreeNonneg_OPEN 1601 := fun r => by
  have hap : (a_p 1601 : ℝ) = 46 := by exact_mod_cast BSD_ap_p1601
  have key : r ^ 2 - (a_p 1601 : ℝ) * r + ((1601 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 4288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=1607: a_p=-41, 4p-a_p²=4747
theorem BSD_DegreeNonneg_p1607 : BSD_FrobeniusDegreeNonneg_OPEN 1607 := fun r => by
  have hap : (a_p 1607 : ℝ) = -41 := by exact_mod_cast BSD_ap_p1607
  have key : r ^ 2 - (a_p 1607 : ℝ) * r + ((1607 : ℕ) : ℝ) =
      (r + 41/2) ^ 2 + 4747/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (41 : ℝ)/2)]

-- p=1609: a_p=-2, 4p-a_p²=6432
theorem BSD_DegreeNonneg_p1609 : BSD_FrobeniusDegreeNonneg_OPEN 1609 := fun r => by
  have hap : (a_p 1609 : ℝ) = -2 := by exact_mod_cast BSD_ap_p1609
  have key : r ^ 2 - (a_p 1609 : ℝ) * r + ((1609 : ℕ) : ℝ) =
      (r + 2/2) ^ 2 + 6432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (2 : ℝ)/2)]

-- p=1613: a_p=-20, 4p-a_p²=6052
theorem BSD_DegreeNonneg_p1613 : BSD_FrobeniusDegreeNonneg_OPEN 1613 := fun r => by
  have hap : (a_p 1613 : ℝ) = -20 := by exact_mod_cast BSD_ap_p1613
  have key : r ^ 2 - (a_p 1613 : ℝ) * r + ((1613 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 6052/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=1619: a_p=-40, 4p-a_p²=4876
theorem BSD_DegreeNonneg_p1619 : BSD_FrobeniusDegreeNonneg_OPEN 1619 := fun r => by
  have hap : (a_p 1619 : ℝ) = -40 := by exact_mod_cast BSD_ap_p1619
  have key : r ^ 2 - (a_p 1619 : ℝ) * r + ((1619 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 4876/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

-- p=1621: a_p=-10, 4p-a_p²=6384
theorem BSD_DegreeNonneg_p1621 : BSD_FrobeniusDegreeNonneg_OPEN 1621 := fun r => by
  have hap : (a_p 1621 : ℝ) = -10 := by exact_mod_cast BSD_ap_p1621
  have key : r ^ 2 - (a_p 1621 : ℝ) * r + ((1621 : ℕ) : ℝ) =
      (r + 10/2) ^ 2 + 6384/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (10 : ℝ)/2)]

-- p=1627: a_p=-8, 4p-a_p²=6444
theorem BSD_DegreeNonneg_p1627 : BSD_FrobeniusDegreeNonneg_OPEN 1627 := fun r => by
  have hap : (a_p 1627 : ℝ) = -8 := by exact_mod_cast BSD_ap_p1627
  have key : r ^ 2 - (a_p 1627 : ℝ) * r + ((1627 : ℕ) : ℝ) =
      (r + 8/2) ^ 2 + 6444/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (8 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1579 : BSD_Hasse_OPEN 1579 :=
  BSD_hasse_of_degree_nonneg 1579 BSD_DegreeNonneg_p1579
theorem BSD_Hasse_OPEN_p1583 : BSD_Hasse_OPEN 1583 :=
  BSD_hasse_of_degree_nonneg 1583 BSD_DegreeNonneg_p1583
theorem BSD_Hasse_OPEN_p1597 : BSD_Hasse_OPEN 1597 :=
  BSD_hasse_of_degree_nonneg 1597 BSD_DegreeNonneg_p1597
theorem BSD_Hasse_OPEN_p1601 : BSD_Hasse_OPEN 1601 :=
  BSD_hasse_of_degree_nonneg 1601 BSD_DegreeNonneg_p1601
theorem BSD_Hasse_OPEN_p1607 : BSD_Hasse_OPEN 1607 :=
  BSD_hasse_of_degree_nonneg 1607 BSD_DegreeNonneg_p1607
theorem BSD_Hasse_OPEN_p1609 : BSD_Hasse_OPEN 1609 :=
  BSD_hasse_of_degree_nonneg 1609 BSD_DegreeNonneg_p1609
theorem BSD_Hasse_OPEN_p1613 : BSD_Hasse_OPEN 1613 :=
  BSD_hasse_of_degree_nonneg 1613 BSD_DegreeNonneg_p1613
theorem BSD_Hasse_OPEN_p1619 : BSD_Hasse_OPEN 1619 :=
  BSD_hasse_of_degree_nonneg 1619 BSD_DegreeNonneg_p1619
theorem BSD_Hasse_OPEN_p1621 : BSD_Hasse_OPEN 1621 :=
  BSD_hasse_of_degree_nonneg 1621 BSD_DegreeNonneg_p1621
theorem BSD_Hasse_OPEN_p1627 : BSD_Hasse_OPEN 1627 :=
  BSD_hasse_of_degree_nonneg 1627 BSD_DegreeNonneg_p1627

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1579 : (a_p 1579 : ℝ) ^ 2 ≤ 4 * (1579 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1579
theorem BSD_HasseBound_Disc_p1583 : (a_p 1583 : ℝ) ^ 2 ≤ 4 * (1583 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1583
theorem BSD_HasseBound_Disc_p1597 : (a_p 1597 : ℝ) ^ 2 ≤ 4 * (1597 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1597
theorem BSD_HasseBound_Disc_p1601 : (a_p 1601 : ℝ) ^ 2 ≤ 4 * (1601 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1601
theorem BSD_HasseBound_Disc_p1607 : (a_p 1607 : ℝ) ^ 2 ≤ 4 * (1607 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1607
theorem BSD_HasseBound_Disc_p1609 : (a_p 1609 : ℝ) ^ 2 ≤ 4 * (1609 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1609
theorem BSD_HasseBound_Disc_p1613 : (a_p 1613 : ℝ) ^ 2 ≤ 4 * (1613 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1613
theorem BSD_HasseBound_Disc_p1619 : (a_p 1619 : ℝ) ^ 2 ≤ 4 * (1619 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1619
theorem BSD_HasseBound_Disc_p1621 : (a_p 1621 : ℝ) ^ 2 ≤ 4 * (1621 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1621
theorem BSD_HasseBound_Disc_p1627 : (a_p 1627 : ℝ) ^ 2 ≤ 4 * (1627 : ℝ) :=
  BSD_disc_from_deg_791 BSD_DegreeNonneg_p1627

end Towers.BSD