/-
================================================================
Towers / BSD / BSD_Genesis793_CLOSED  (genesis-793)

HasseBridge Tier C: Hasse bounds for primes
1723..1789 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1723: card=1666, a_p=+58, disc=-3528
  p=1733: card=1690, a_p=+44, disc=-4996
  p=1741: card=1749, a_p=-7, disc=-6915
  p=1747: card=1803, a_p=-55, disc=-3963
  p=1753: card=1804, a_p=-50, disc=-4512
  p=1759: card=1758, a_p=+2, disc=-7032
  p=1777: card=1774, a_p=+4, disc=-7092
  p=1783: card=1759, a_p=+25, disc=-6507
  p=1787: card=1815, a_p=-27, disc=-6419
  p=1789: card=1772, a_p=+18, disc=-6832

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_793 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i793_p1723 : Fact (1723 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1733 : Fact (1733 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1741 : Fact (1741 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1747 : Fact (1747 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1753 : Fact (1753 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1759 : Fact (1759 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1777 : Fact (1777 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1783 : Fact (1783 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1787 : Fact (1787 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1789 : Fact (1789 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1723 : (E143_Finset 1723).card = 1666 := by native_decide
theorem BSD_E143_card_p1733 : (E143_Finset 1733).card = 1690 := by native_decide
theorem BSD_E143_card_p1741 : (E143_Finset 1741).card = 1749 := by native_decide
theorem BSD_E143_card_p1747 : (E143_Finset 1747).card = 1803 := by native_decide
theorem BSD_E143_card_p1753 : (E143_Finset 1753).card = 1804 := by native_decide
theorem BSD_E143_card_p1759 : (E143_Finset 1759).card = 1758 := by native_decide
theorem BSD_E143_card_p1777 : (E143_Finset 1777).card = 1774 := by native_decide
theorem BSD_E143_card_p1783 : (E143_Finset 1783).card = 1759 := by native_decide
theorem BSD_E143_card_p1787 : (E143_Finset 1787).card = 1815 := by native_decide
theorem BSD_E143_card_p1789 : (E143_Finset 1789).card = 1772 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1723 : a_p 1723 = (58 : ℤ) := by
  have h := BSD_E143_card_p1723; unfold a_p; omega
theorem BSD_ap_p1733 : a_p 1733 = (44 : ℤ) := by
  have h := BSD_E143_card_p1733; unfold a_p; omega
theorem BSD_ap_p1741 : a_p 1741 = (-7 : ℤ) := by
  have h := BSD_E143_card_p1741; unfold a_p; omega
theorem BSD_ap_p1747 : a_p 1747 = (-55 : ℤ) := by
  have h := BSD_E143_card_p1747; unfold a_p; omega
theorem BSD_ap_p1753 : a_p 1753 = (-50 : ℤ) := by
  have h := BSD_E143_card_p1753; unfold a_p; omega
theorem BSD_ap_p1759 : a_p 1759 = (2 : ℤ) := by
  have h := BSD_E143_card_p1759; unfold a_p; omega
theorem BSD_ap_p1777 : a_p 1777 = (4 : ℤ) := by
  have h := BSD_E143_card_p1777; unfold a_p; omega
theorem BSD_ap_p1783 : a_p 1783 = (25 : ℤ) := by
  have h := BSD_E143_card_p1783; unfold a_p; omega
theorem BSD_ap_p1787 : a_p 1787 = (-27 : ℤ) := by
  have h := BSD_E143_card_p1787; unfold a_p; omega
theorem BSD_ap_p1789 : a_p 1789 = (18 : ℤ) := by
  have h := BSD_E143_card_p1789; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1723: a_p=+58, 4p-a_p²=3528
theorem BSD_DegreeNonneg_p1723 : BSD_FrobeniusDegreeNonneg_OPEN 1723 := fun r => by
  have hap : (a_p 1723 : ℝ) = 58 := by exact_mod_cast BSD_ap_p1723
  have key : r ^ 2 - (a_p 1723 : ℝ) * r + ((1723 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 3528/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

-- p=1733: a_p=+44, 4p-a_p²=4996
theorem BSD_DegreeNonneg_p1733 : BSD_FrobeniusDegreeNonneg_OPEN 1733 := fun r => by
  have hap : (a_p 1733 : ℝ) = 44 := by exact_mod_cast BSD_ap_p1733
  have key : r ^ 2 - (a_p 1733 : ℝ) * r + ((1733 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 4996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

-- p=1741: a_p=-7, 4p-a_p²=6915
theorem BSD_DegreeNonneg_p1741 : BSD_FrobeniusDegreeNonneg_OPEN 1741 := fun r => by
  have hap : (a_p 1741 : ℝ) = -7 := by exact_mod_cast BSD_ap_p1741
  have key : r ^ 2 - (a_p 1741 : ℝ) * r + ((1741 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 6915/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

-- p=1747: a_p=-55, 4p-a_p²=3963
theorem BSD_DegreeNonneg_p1747 : BSD_FrobeniusDegreeNonneg_OPEN 1747 := fun r => by
  have hap : (a_p 1747 : ℝ) = -55 := by exact_mod_cast BSD_ap_p1747
  have key : r ^ 2 - (a_p 1747 : ℝ) * r + ((1747 : ℕ) : ℝ) =
      (r + 55/2) ^ 2 + 3963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (55 : ℝ)/2)]

-- p=1753: a_p=-50, 4p-a_p²=4512
theorem BSD_DegreeNonneg_p1753 : BSD_FrobeniusDegreeNonneg_OPEN 1753 := fun r => by
  have hap : (a_p 1753 : ℝ) = -50 := by exact_mod_cast BSD_ap_p1753
  have key : r ^ 2 - (a_p 1753 : ℝ) * r + ((1753 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 4512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

-- p=1759: a_p=+2, 4p-a_p²=7032
theorem BSD_DegreeNonneg_p1759 : BSD_FrobeniusDegreeNonneg_OPEN 1759 := fun r => by
  have hap : (a_p 1759 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1759
  have key : r ^ 2 - (a_p 1759 : ℝ) * r + ((1759 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 7032/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

-- p=1777: a_p=+4, 4p-a_p²=7092
theorem BSD_DegreeNonneg_p1777 : BSD_FrobeniusDegreeNonneg_OPEN 1777 := fun r => by
  have hap : (a_p 1777 : ℝ) = 4 := by exact_mod_cast BSD_ap_p1777
  have key : r ^ 2 - (a_p 1777 : ℝ) * r + ((1777 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 7092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

-- p=1783: a_p=+25, 4p-a_p²=6507
theorem BSD_DegreeNonneg_p1783 : BSD_FrobeniusDegreeNonneg_OPEN 1783 := fun r => by
  have hap : (a_p 1783 : ℝ) = 25 := by exact_mod_cast BSD_ap_p1783
  have key : r ^ 2 - (a_p 1783 : ℝ) * r + ((1783 : ℕ) : ℝ) =
      (r - 25/2) ^ 2 + 6507/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (25 : ℝ)/2)]

-- p=1787: a_p=-27, 4p-a_p²=6419
theorem BSD_DegreeNonneg_p1787 : BSD_FrobeniusDegreeNonneg_OPEN 1787 := fun r => by
  have hap : (a_p 1787 : ℝ) = -27 := by exact_mod_cast BSD_ap_p1787
  have key : r ^ 2 - (a_p 1787 : ℝ) * r + ((1787 : ℕ) : ℝ) =
      (r + 27/2) ^ 2 + 6419/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (27 : ℝ)/2)]

-- p=1789: a_p=+18, 4p-a_p²=6832
theorem BSD_DegreeNonneg_p1789 : BSD_FrobeniusDegreeNonneg_OPEN 1789 := fun r => by
  have hap : (a_p 1789 : ℝ) = 18 := by exact_mod_cast BSD_ap_p1789
  have key : r ^ 2 - (a_p 1789 : ℝ) * r + ((1789 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 6832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1723 : BSD_Hasse_OPEN 1723 :=
  BSD_hasse_of_degree_nonneg 1723 BSD_DegreeNonneg_p1723
theorem BSD_Hasse_OPEN_p1733 : BSD_Hasse_OPEN 1733 :=
  BSD_hasse_of_degree_nonneg 1733 BSD_DegreeNonneg_p1733
theorem BSD_Hasse_OPEN_p1741 : BSD_Hasse_OPEN 1741 :=
  BSD_hasse_of_degree_nonneg 1741 BSD_DegreeNonneg_p1741
theorem BSD_Hasse_OPEN_p1747 : BSD_Hasse_OPEN 1747 :=
  BSD_hasse_of_degree_nonneg 1747 BSD_DegreeNonneg_p1747
theorem BSD_Hasse_OPEN_p1753 : BSD_Hasse_OPEN 1753 :=
  BSD_hasse_of_degree_nonneg 1753 BSD_DegreeNonneg_p1753
theorem BSD_Hasse_OPEN_p1759 : BSD_Hasse_OPEN 1759 :=
  BSD_hasse_of_degree_nonneg 1759 BSD_DegreeNonneg_p1759
theorem BSD_Hasse_OPEN_p1777 : BSD_Hasse_OPEN 1777 :=
  BSD_hasse_of_degree_nonneg 1777 BSD_DegreeNonneg_p1777
theorem BSD_Hasse_OPEN_p1783 : BSD_Hasse_OPEN 1783 :=
  BSD_hasse_of_degree_nonneg 1783 BSD_DegreeNonneg_p1783
theorem BSD_Hasse_OPEN_p1787 : BSD_Hasse_OPEN 1787 :=
  BSD_hasse_of_degree_nonneg 1787 BSD_DegreeNonneg_p1787
theorem BSD_Hasse_OPEN_p1789 : BSD_Hasse_OPEN 1789 :=
  BSD_hasse_of_degree_nonneg 1789 BSD_DegreeNonneg_p1789

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1723 : (a_p 1723 : ℝ) ^ 2 ≤ 4 * (1723 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1723
theorem BSD_HasseBound_Disc_p1733 : (a_p 1733 : ℝ) ^ 2 ≤ 4 * (1733 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1733
theorem BSD_HasseBound_Disc_p1741 : (a_p 1741 : ℝ) ^ 2 ≤ 4 * (1741 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1741
theorem BSD_HasseBound_Disc_p1747 : (a_p 1747 : ℝ) ^ 2 ≤ 4 * (1747 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1747
theorem BSD_HasseBound_Disc_p1753 : (a_p 1753 : ℝ) ^ 2 ≤ 4 * (1753 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1753
theorem BSD_HasseBound_Disc_p1759 : (a_p 1759 : ℝ) ^ 2 ≤ 4 * (1759 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1759
theorem BSD_HasseBound_Disc_p1777 : (a_p 1777 : ℝ) ^ 2 ≤ 4 * (1777 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1777
theorem BSD_HasseBound_Disc_p1783 : (a_p 1783 : ℝ) ^ 2 ≤ 4 * (1783 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1783
theorem BSD_HasseBound_Disc_p1787 : (a_p 1787 : ℝ) ^ 2 ≤ 4 * (1787 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1787
theorem BSD_HasseBound_Disc_p1789 : (a_p 1789 : ℝ) ^ 2 ≤ 4 * (1789 : ℝ) :=
  BSD_disc_from_deg_793 BSD_DegreeNonneg_p1789

end Towers.BSD