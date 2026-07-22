/-
================================================================
Towers / BSD / BSD_Genesis792_CLOSED  (genesis-792)

HasseBridge Tier C: Hasse bounds for primes
1637..1721 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1637: card=1665, a_p=-27, disc=-5819
  p=1657: card=1624, a_p=+34, disc=-5472
  p=1663: card=1722, a_p=-58, disc=-3288
  p=1667: card=1634, a_p=+34, disc=-5512
  p=1669: card=1716, a_p=-46, disc=-4560
  p=1693: card=1750, a_p=-56, disc=-3636
  p=1697: card=1632, a_p=+66, disc=-2432
  p=1699: card=1688, a_p=+12, disc=-6652
  p=1709: card=1665, a_p=+45, disc=-4811
  p=1721: card=1683, a_p=+39, disc=-5363

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_792 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i792_p1637 : Fact (1637 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1657 : Fact (1657 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1663 : Fact (1663 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1667 : Fact (1667 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1669 : Fact (1669 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1693 : Fact (1693 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1697 : Fact (1697 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1699 : Fact (1699 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1709 : Fact (1709 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1721 : Fact (1721 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1637 : (E143_Finset 1637).card = 1665 := by native_decide
theorem BSD_E143_card_p1657 : (E143_Finset 1657).card = 1624 := by native_decide
theorem BSD_E143_card_p1663 : (E143_Finset 1663).card = 1722 := by native_decide
theorem BSD_E143_card_p1667 : (E143_Finset 1667).card = 1634 := by native_decide
theorem BSD_E143_card_p1669 : (E143_Finset 1669).card = 1716 := by native_decide
theorem BSD_E143_card_p1693 : (E143_Finset 1693).card = 1750 := by native_decide
theorem BSD_E143_card_p1697 : (E143_Finset 1697).card = 1632 := by native_decide
theorem BSD_E143_card_p1699 : (E143_Finset 1699).card = 1688 := by native_decide
theorem BSD_E143_card_p1709 : (E143_Finset 1709).card = 1665 := by native_decide
theorem BSD_E143_card_p1721 : (E143_Finset 1721).card = 1683 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1637 : a_p 1637 = (-27 : ℤ) := by
  have h := BSD_E143_card_p1637; unfold a_p; omega
theorem BSD_ap_p1657 : a_p 1657 = (34 : ℤ) := by
  have h := BSD_E143_card_p1657; unfold a_p; omega
theorem BSD_ap_p1663 : a_p 1663 = (-58 : ℤ) := by
  have h := BSD_E143_card_p1663; unfold a_p; omega
theorem BSD_ap_p1667 : a_p 1667 = (34 : ℤ) := by
  have h := BSD_E143_card_p1667; unfold a_p; omega
theorem BSD_ap_p1669 : a_p 1669 = (-46 : ℤ) := by
  have h := BSD_E143_card_p1669; unfold a_p; omega
theorem BSD_ap_p1693 : a_p 1693 = (-56 : ℤ) := by
  have h := BSD_E143_card_p1693; unfold a_p; omega
theorem BSD_ap_p1697 : a_p 1697 = (66 : ℤ) := by
  have h := BSD_E143_card_p1697; unfold a_p; omega
theorem BSD_ap_p1699 : a_p 1699 = (12 : ℤ) := by
  have h := BSD_E143_card_p1699; unfold a_p; omega
theorem BSD_ap_p1709 : a_p 1709 = (45 : ℤ) := by
  have h := BSD_E143_card_p1709; unfold a_p; omega
theorem BSD_ap_p1721 : a_p 1721 = (39 : ℤ) := by
  have h := BSD_E143_card_p1721; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1637: a_p=-27, 4p-a_p²=5819
theorem BSD_DegreeNonneg_p1637 : BSD_FrobeniusDegreeNonneg_OPEN 1637 := fun r => by
  have hap : (a_p 1637 : ℝ) = -27 := by exact_mod_cast BSD_ap_p1637
  have key : r ^ 2 - (a_p 1637 : ℝ) * r + ((1637 : ℕ) : ℝ) =
      (r + 27/2) ^ 2 + 5819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (27 : ℝ)/2)]

-- p=1657: a_p=+34, 4p-a_p²=5472
theorem BSD_DegreeNonneg_p1657 : BSD_FrobeniusDegreeNonneg_OPEN 1657 := fun r => by
  have hap : (a_p 1657 : ℝ) = 34 := by exact_mod_cast BSD_ap_p1657
  have key : r ^ 2 - (a_p 1657 : ℝ) * r + ((1657 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 5472/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

-- p=1663: a_p=-58, 4p-a_p²=3288
theorem BSD_DegreeNonneg_p1663 : BSD_FrobeniusDegreeNonneg_OPEN 1663 := fun r => by
  have hap : (a_p 1663 : ℝ) = -58 := by exact_mod_cast BSD_ap_p1663
  have key : r ^ 2 - (a_p 1663 : ℝ) * r + ((1663 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 3288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=1667: a_p=+34, 4p-a_p²=5512
theorem BSD_DegreeNonneg_p1667 : BSD_FrobeniusDegreeNonneg_OPEN 1667 := fun r => by
  have hap : (a_p 1667 : ℝ) = 34 := by exact_mod_cast BSD_ap_p1667
  have key : r ^ 2 - (a_p 1667 : ℝ) * r + ((1667 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 5512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

-- p=1669: a_p=-46, 4p-a_p²=4560
theorem BSD_DegreeNonneg_p1669 : BSD_FrobeniusDegreeNonneg_OPEN 1669 := fun r => by
  have hap : (a_p 1669 : ℝ) = -46 := by exact_mod_cast BSD_ap_p1669
  have key : r ^ 2 - (a_p 1669 : ℝ) * r + ((1669 : ℕ) : ℝ) =
      (r + 46/2) ^ 2 + 4560/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (46 : ℝ)/2)]

-- p=1693: a_p=-56, 4p-a_p²=3636
theorem BSD_DegreeNonneg_p1693 : BSD_FrobeniusDegreeNonneg_OPEN 1693 := fun r => by
  have hap : (a_p 1693 : ℝ) = -56 := by exact_mod_cast BSD_ap_p1693
  have key : r ^ 2 - (a_p 1693 : ℝ) * r + ((1693 : ℕ) : ℝ) =
      (r + 56/2) ^ 2 + 3636/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (56 : ℝ)/2)]

-- p=1697: a_p=+66, 4p-a_p²=2432
theorem BSD_DegreeNonneg_p1697 : BSD_FrobeniusDegreeNonneg_OPEN 1697 := fun r => by
  have hap : (a_p 1697 : ℝ) = 66 := by exact_mod_cast BSD_ap_p1697
  have key : r ^ 2 - (a_p 1697 : ℝ) * r + ((1697 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 2432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

-- p=1699: a_p=+12, 4p-a_p²=6652
theorem BSD_DegreeNonneg_p1699 : BSD_FrobeniusDegreeNonneg_OPEN 1699 := fun r => by
  have hap : (a_p 1699 : ℝ) = 12 := by exact_mod_cast BSD_ap_p1699
  have key : r ^ 2 - (a_p 1699 : ℝ) * r + ((1699 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 6652/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=1709: a_p=+45, 4p-a_p²=4811
theorem BSD_DegreeNonneg_p1709 : BSD_FrobeniusDegreeNonneg_OPEN 1709 := fun r => by
  have hap : (a_p 1709 : ℝ) = 45 := by exact_mod_cast BSD_ap_p1709
  have key : r ^ 2 - (a_p 1709 : ℝ) * r + ((1709 : ℕ) : ℝ) =
      (r - 45/2) ^ 2 + 4811/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (45 : ℝ)/2)]

-- p=1721: a_p=+39, 4p-a_p²=5363
theorem BSD_DegreeNonneg_p1721 : BSD_FrobeniusDegreeNonneg_OPEN 1721 := fun r => by
  have hap : (a_p 1721 : ℝ) = 39 := by exact_mod_cast BSD_ap_p1721
  have key : r ^ 2 - (a_p 1721 : ℝ) * r + ((1721 : ℕ) : ℝ) =
      (r - 39/2) ^ 2 + 5363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (39 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1637 : BSD_Hasse_OPEN 1637 :=
  BSD_hasse_of_degree_nonneg 1637 BSD_DegreeNonneg_p1637
theorem BSD_Hasse_OPEN_p1657 : BSD_Hasse_OPEN 1657 :=
  BSD_hasse_of_degree_nonneg 1657 BSD_DegreeNonneg_p1657
theorem BSD_Hasse_OPEN_p1663 : BSD_Hasse_OPEN 1663 :=
  BSD_hasse_of_degree_nonneg 1663 BSD_DegreeNonneg_p1663
theorem BSD_Hasse_OPEN_p1667 : BSD_Hasse_OPEN 1667 :=
  BSD_hasse_of_degree_nonneg 1667 BSD_DegreeNonneg_p1667
theorem BSD_Hasse_OPEN_p1669 : BSD_Hasse_OPEN 1669 :=
  BSD_hasse_of_degree_nonneg 1669 BSD_DegreeNonneg_p1669
theorem BSD_Hasse_OPEN_p1693 : BSD_Hasse_OPEN 1693 :=
  BSD_hasse_of_degree_nonneg 1693 BSD_DegreeNonneg_p1693
theorem BSD_Hasse_OPEN_p1697 : BSD_Hasse_OPEN 1697 :=
  BSD_hasse_of_degree_nonneg 1697 BSD_DegreeNonneg_p1697
theorem BSD_Hasse_OPEN_p1699 : BSD_Hasse_OPEN 1699 :=
  BSD_hasse_of_degree_nonneg 1699 BSD_DegreeNonneg_p1699
theorem BSD_Hasse_OPEN_p1709 : BSD_Hasse_OPEN 1709 :=
  BSD_hasse_of_degree_nonneg 1709 BSD_DegreeNonneg_p1709
theorem BSD_Hasse_OPEN_p1721 : BSD_Hasse_OPEN 1721 :=
  BSD_hasse_of_degree_nonneg 1721 BSD_DegreeNonneg_p1721

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1637 : (a_p 1637 : ℝ) ^ 2 ≤ 4 * (1637 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1637
theorem BSD_HasseBound_Disc_p1657 : (a_p 1657 : ℝ) ^ 2 ≤ 4 * (1657 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1657
theorem BSD_HasseBound_Disc_p1663 : (a_p 1663 : ℝ) ^ 2 ≤ 4 * (1663 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1663
theorem BSD_HasseBound_Disc_p1667 : (a_p 1667 : ℝ) ^ 2 ≤ 4 * (1667 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1667
theorem BSD_HasseBound_Disc_p1669 : (a_p 1669 : ℝ) ^ 2 ≤ 4 * (1669 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1669
theorem BSD_HasseBound_Disc_p1693 : (a_p 1693 : ℝ) ^ 2 ≤ 4 * (1693 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1693
theorem BSD_HasseBound_Disc_p1697 : (a_p 1697 : ℝ) ^ 2 ≤ 4 * (1697 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1697
theorem BSD_HasseBound_Disc_p1699 : (a_p 1699 : ℝ) ^ 2 ≤ 4 * (1699 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1699
theorem BSD_HasseBound_Disc_p1709 : (a_p 1709 : ℝ) ^ 2 ≤ 4 * (1709 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1709
theorem BSD_HasseBound_Disc_p1721 : (a_p 1721 : ℝ) ^ 2 ≤ 4 * (1721 : ℝ) :=
  BSD_disc_from_deg_792 BSD_DegreeNonneg_p1721

end Towers.BSD