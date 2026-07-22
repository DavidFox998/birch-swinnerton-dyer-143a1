/-
================================================================
Towers / BSD / BSD_Genesis805_CLOSED  (genesis-805)

HasseBridge Tier C: Hasse bounds for primes
2683..2729 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2683: card=2736, a_p=-52, disc=-8028
  p=2687: card=2681, a_p=+7, disc=-10699
  p=2689: card=2767, a_p=-77, disc=-4827
  p=2693: card=2757, a_p=-63, disc=-6803
  p=2699: card=2709, a_p=-9, disc=-10715
  p=2707: card=2685, a_p=+23, disc=-10299
  p=2711: card=2631, a_p=+81, disc=-4283
  p=2713: card=2656, a_p=+58, disc=-7488
  p=2719: card=2734, a_p=-14, disc=-10680
  p=2729: card=2676, a_p=+54, disc=-8000

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_805 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i805_p2683 : Fact (2683 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2687 : Fact (2687 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2689 : Fact (2689 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2693 : Fact (2693 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2699 : Fact (2699 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2707 : Fact (2707 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2711 : Fact (2711 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2713 : Fact (2713 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2719 : Fact (2719 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2729 : Fact (2729 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2683 : (E143_Finset 2683).card = 2736 := by native_decide
theorem BSD_E143_card_p2687 : (E143_Finset 2687).card = 2681 := by native_decide
theorem BSD_E143_card_p2689 : (E143_Finset 2689).card = 2767 := by native_decide
theorem BSD_E143_card_p2693 : (E143_Finset 2693).card = 2757 := by native_decide
theorem BSD_E143_card_p2699 : (E143_Finset 2699).card = 2709 := by native_decide
theorem BSD_E143_card_p2707 : (E143_Finset 2707).card = 2685 := by native_decide
theorem BSD_E143_card_p2711 : (E143_Finset 2711).card = 2631 := by native_decide
theorem BSD_E143_card_p2713 : (E143_Finset 2713).card = 2656 := by native_decide
theorem BSD_E143_card_p2719 : (E143_Finset 2719).card = 2734 := by native_decide
theorem BSD_E143_card_p2729 : (E143_Finset 2729).card = 2676 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2683 : a_p 2683 = (-52 : ℤ) := by
  have h := BSD_E143_card_p2683; unfold a_p; omega
theorem BSD_ap_p2687 : a_p 2687 = (7 : ℤ) := by
  have h := BSD_E143_card_p2687; unfold a_p; omega
theorem BSD_ap_p2689 : a_p 2689 = (-77 : ℤ) := by
  have h := BSD_E143_card_p2689; unfold a_p; omega
theorem BSD_ap_p2693 : a_p 2693 = (-63 : ℤ) := by
  have h := BSD_E143_card_p2693; unfold a_p; omega
theorem BSD_ap_p2699 : a_p 2699 = (-9 : ℤ) := by
  have h := BSD_E143_card_p2699; unfold a_p; omega
theorem BSD_ap_p2707 : a_p 2707 = (23 : ℤ) := by
  have h := BSD_E143_card_p2707; unfold a_p; omega
theorem BSD_ap_p2711 : a_p 2711 = (81 : ℤ) := by
  have h := BSD_E143_card_p2711; unfold a_p; omega
theorem BSD_ap_p2713 : a_p 2713 = (58 : ℤ) := by
  have h := BSD_E143_card_p2713; unfold a_p; omega
theorem BSD_ap_p2719 : a_p 2719 = (-14 : ℤ) := by
  have h := BSD_E143_card_p2719; unfold a_p; omega
theorem BSD_ap_p2729 : a_p 2729 = (54 : ℤ) := by
  have h := BSD_E143_card_p2729; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2683: a_p=-52, 4p-a_p²=8028
theorem BSD_DegreeNonneg_p2683 : BSD_FrobeniusDegreeNonneg_OPEN 2683 := fun r => by
  have hap : (a_p 2683 : ℝ) = -52 := by exact_mod_cast BSD_ap_p2683
  have key : r ^ 2 - (a_p 2683 : ℝ) * r + ((2683 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 8028/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

-- p=2687: a_p=+7, 4p-a_p²=10699
theorem BSD_DegreeNonneg_p2687 : BSD_FrobeniusDegreeNonneg_OPEN 2687 := fun r => by
  have hap : (a_p 2687 : ℝ) = 7 := by exact_mod_cast BSD_ap_p2687
  have key : r ^ 2 - (a_p 2687 : ℝ) * r + ((2687 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 10699/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

-- p=2689: a_p=-77, 4p-a_p²=4827
theorem BSD_DegreeNonneg_p2689 : BSD_FrobeniusDegreeNonneg_OPEN 2689 := fun r => by
  have hap : (a_p 2689 : ℝ) = -77 := by exact_mod_cast BSD_ap_p2689
  have key : r ^ 2 - (a_p 2689 : ℝ) * r + ((2689 : ℕ) : ℝ) =
      (r + 77/2) ^ 2 + 4827/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (77 : ℝ)/2)]

-- p=2693: a_p=-63, 4p-a_p²=6803
theorem BSD_DegreeNonneg_p2693 : BSD_FrobeniusDegreeNonneg_OPEN 2693 := fun r => by
  have hap : (a_p 2693 : ℝ) = -63 := by exact_mod_cast BSD_ap_p2693
  have key : r ^ 2 - (a_p 2693 : ℝ) * r + ((2693 : ℕ) : ℝ) =
      (r + 63/2) ^ 2 + 6803/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (63 : ℝ)/2)]

-- p=2699: a_p=-9, 4p-a_p²=10715
theorem BSD_DegreeNonneg_p2699 : BSD_FrobeniusDegreeNonneg_OPEN 2699 := fun r => by
  have hap : (a_p 2699 : ℝ) = -9 := by exact_mod_cast BSD_ap_p2699
  have key : r ^ 2 - (a_p 2699 : ℝ) * r + ((2699 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 10715/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

-- p=2707: a_p=+23, 4p-a_p²=10299
theorem BSD_DegreeNonneg_p2707 : BSD_FrobeniusDegreeNonneg_OPEN 2707 := fun r => by
  have hap : (a_p 2707 : ℝ) = 23 := by exact_mod_cast BSD_ap_p2707
  have key : r ^ 2 - (a_p 2707 : ℝ) * r + ((2707 : ℕ) : ℝ) =
      (r - 23/2) ^ 2 + 10299/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (23 : ℝ)/2)]

-- p=2711: a_p=+81, 4p-a_p²=4283
theorem BSD_DegreeNonneg_p2711 : BSD_FrobeniusDegreeNonneg_OPEN 2711 := fun r => by
  have hap : (a_p 2711 : ℝ) = 81 := by exact_mod_cast BSD_ap_p2711
  have key : r ^ 2 - (a_p 2711 : ℝ) * r + ((2711 : ℕ) : ℝ) =
      (r - 81/2) ^ 2 + 4283/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (81 : ℝ)/2)]

-- p=2713: a_p=+58, 4p-a_p²=7488
theorem BSD_DegreeNonneg_p2713 : BSD_FrobeniusDegreeNonneg_OPEN 2713 := fun r => by
  have hap : (a_p 2713 : ℝ) = 58 := by exact_mod_cast BSD_ap_p2713
  have key : r ^ 2 - (a_p 2713 : ℝ) * r + ((2713 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 7488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

-- p=2719: a_p=-14, 4p-a_p²=10680
theorem BSD_DegreeNonneg_p2719 : BSD_FrobeniusDegreeNonneg_OPEN 2719 := fun r => by
  have hap : (a_p 2719 : ℝ) = -14 := by exact_mod_cast BSD_ap_p2719
  have key : r ^ 2 - (a_p 2719 : ℝ) * r + ((2719 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 10680/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

-- p=2729: a_p=+54, 4p-a_p²=8000
theorem BSD_DegreeNonneg_p2729 : BSD_FrobeniusDegreeNonneg_OPEN 2729 := fun r => by
  have hap : (a_p 2729 : ℝ) = 54 := by exact_mod_cast BSD_ap_p2729
  have key : r ^ 2 - (a_p 2729 : ℝ) * r + ((2729 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 8000/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2683 : BSD_Hasse_OPEN 2683 :=
  BSD_hasse_of_degree_nonneg 2683 BSD_DegreeNonneg_p2683
theorem BSD_Hasse_OPEN_p2687 : BSD_Hasse_OPEN 2687 :=
  BSD_hasse_of_degree_nonneg 2687 BSD_DegreeNonneg_p2687
theorem BSD_Hasse_OPEN_p2689 : BSD_Hasse_OPEN 2689 :=
  BSD_hasse_of_degree_nonneg 2689 BSD_DegreeNonneg_p2689
theorem BSD_Hasse_OPEN_p2693 : BSD_Hasse_OPEN 2693 :=
  BSD_hasse_of_degree_nonneg 2693 BSD_DegreeNonneg_p2693
theorem BSD_Hasse_OPEN_p2699 : BSD_Hasse_OPEN 2699 :=
  BSD_hasse_of_degree_nonneg 2699 BSD_DegreeNonneg_p2699
theorem BSD_Hasse_OPEN_p2707 : BSD_Hasse_OPEN 2707 :=
  BSD_hasse_of_degree_nonneg 2707 BSD_DegreeNonneg_p2707
theorem BSD_Hasse_OPEN_p2711 : BSD_Hasse_OPEN 2711 :=
  BSD_hasse_of_degree_nonneg 2711 BSD_DegreeNonneg_p2711
theorem BSD_Hasse_OPEN_p2713 : BSD_Hasse_OPEN 2713 :=
  BSD_hasse_of_degree_nonneg 2713 BSD_DegreeNonneg_p2713
theorem BSD_Hasse_OPEN_p2719 : BSD_Hasse_OPEN 2719 :=
  BSD_hasse_of_degree_nonneg 2719 BSD_DegreeNonneg_p2719
theorem BSD_Hasse_OPEN_p2729 : BSD_Hasse_OPEN 2729 :=
  BSD_hasse_of_degree_nonneg 2729 BSD_DegreeNonneg_p2729

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2683 : (a_p 2683 : ℝ) ^ 2 ≤ 4 * (2683 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2683
theorem BSD_HasseBound_Disc_p2687 : (a_p 2687 : ℝ) ^ 2 ≤ 4 * (2687 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2687
theorem BSD_HasseBound_Disc_p2689 : (a_p 2689 : ℝ) ^ 2 ≤ 4 * (2689 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2689
theorem BSD_HasseBound_Disc_p2693 : (a_p 2693 : ℝ) ^ 2 ≤ 4 * (2693 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2693
theorem BSD_HasseBound_Disc_p2699 : (a_p 2699 : ℝ) ^ 2 ≤ 4 * (2699 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2699
theorem BSD_HasseBound_Disc_p2707 : (a_p 2707 : ℝ) ^ 2 ≤ 4 * (2707 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2707
theorem BSD_HasseBound_Disc_p2711 : (a_p 2711 : ℝ) ^ 2 ≤ 4 * (2711 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2711
theorem BSD_HasseBound_Disc_p2713 : (a_p 2713 : ℝ) ^ 2 ≤ 4 * (2713 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2713
theorem BSD_HasseBound_Disc_p2719 : (a_p 2719 : ℝ) ^ 2 ≤ 4 * (2719 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2719
theorem BSD_HasseBound_Disc_p2729 : (a_p 2729 : ℝ) ^ 2 ≤ 4 * (2729 : ℝ) :=
  BSD_disc_from_deg_805 BSD_DegreeNonneg_p2729

end Towers.BSD