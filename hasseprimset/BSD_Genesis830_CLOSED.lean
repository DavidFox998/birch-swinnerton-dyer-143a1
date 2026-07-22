/-
================================================================
Towers / BSD / BSD_Genesis830_CLOSED  (genesis-830)

HasseBridge Tier C: Hasse bounds for primes
4733..4813 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4733: card=4665, a_p=+69, disc=-14171
  p=4751: card=4836, a_p=-84, disc=-11948
  p=4759: card=4732, a_p=+28, disc=-18252
  p=4783: card=4733, a_p=+51, disc=-16531
  p=4787: card=4816, a_p=-28, disc=-18364
  p=4789: card=4876, a_p=-86, disc=-11760
  p=4793: card=4852, a_p=-58, disc=-15808
  p=4799: card=4753, a_p=+47, disc=-16987
  p=4801: card=4877, a_p=-75, disc=-13579
  p=4813: card=4898, a_p=-84, disc=-12196

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_830 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i830_p4733 : Fact (4733 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4751 : Fact (4751 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4759 : Fact (4759 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4783 : Fact (4783 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4787 : Fact (4787 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4789 : Fact (4789 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4793 : Fact (4793 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4799 : Fact (4799 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4801 : Fact (4801 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4813 : Fact (4813 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4733 : (E143_Finset 4733).card = 4665 := by native_decide
theorem BSD_E143_card_p4751 : (E143_Finset 4751).card = 4836 := by native_decide
theorem BSD_E143_card_p4759 : (E143_Finset 4759).card = 4732 := by native_decide
theorem BSD_E143_card_p4783 : (E143_Finset 4783).card = 4733 := by native_decide
theorem BSD_E143_card_p4787 : (E143_Finset 4787).card = 4816 := by native_decide
theorem BSD_E143_card_p4789 : (E143_Finset 4789).card = 4876 := by native_decide
theorem BSD_E143_card_p4793 : (E143_Finset 4793).card = 4852 := by native_decide
theorem BSD_E143_card_p4799 : (E143_Finset 4799).card = 4753 := by native_decide
theorem BSD_E143_card_p4801 : (E143_Finset 4801).card = 4877 := by native_decide
theorem BSD_E143_card_p4813 : (E143_Finset 4813).card = 4898 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4733 : a_p 4733 = (69 : ℤ) := by
  have h := BSD_E143_card_p4733; unfold a_p; omega
theorem BSD_ap_p4751 : a_p 4751 = (-84 : ℤ) := by
  have h := BSD_E143_card_p4751; unfold a_p; omega
theorem BSD_ap_p4759 : a_p 4759 = (28 : ℤ) := by
  have h := BSD_E143_card_p4759; unfold a_p; omega
theorem BSD_ap_p4783 : a_p 4783 = (51 : ℤ) := by
  have h := BSD_E143_card_p4783; unfold a_p; omega
theorem BSD_ap_p4787 : a_p 4787 = (-28 : ℤ) := by
  have h := BSD_E143_card_p4787; unfold a_p; omega
theorem BSD_ap_p4789 : a_p 4789 = (-86 : ℤ) := by
  have h := BSD_E143_card_p4789; unfold a_p; omega
theorem BSD_ap_p4793 : a_p 4793 = (-58 : ℤ) := by
  have h := BSD_E143_card_p4793; unfold a_p; omega
theorem BSD_ap_p4799 : a_p 4799 = (47 : ℤ) := by
  have h := BSD_E143_card_p4799; unfold a_p; omega
theorem BSD_ap_p4801 : a_p 4801 = (-75 : ℤ) := by
  have h := BSD_E143_card_p4801; unfold a_p; omega
theorem BSD_ap_p4813 : a_p 4813 = (-84 : ℤ) := by
  have h := BSD_E143_card_p4813; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4733: a_p=+69, 4p-a_p²=14171
theorem BSD_DegreeNonneg_p4733 : BSD_FrobeniusDegreeNonneg_OPEN 4733 := fun r => by
  have hap : (a_p 4733 : ℝ) = 69 := by exact_mod_cast BSD_ap_p4733
  have key : r ^ 2 - (a_p 4733 : ℝ) * r + ((4733 : ℕ) : ℝ) =
      (r - 69/2) ^ 2 + 14171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (69 : ℝ)/2)]

-- p=4751: a_p=-84, 4p-a_p²=11948
theorem BSD_DegreeNonneg_p4751 : BSD_FrobeniusDegreeNonneg_OPEN 4751 := fun r => by
  have hap : (a_p 4751 : ℝ) = -84 := by exact_mod_cast BSD_ap_p4751
  have key : r ^ 2 - (a_p 4751 : ℝ) * r + ((4751 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 11948/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

-- p=4759: a_p=+28, 4p-a_p²=18252
theorem BSD_DegreeNonneg_p4759 : BSD_FrobeniusDegreeNonneg_OPEN 4759 := fun r => by
  have hap : (a_p 4759 : ℝ) = 28 := by exact_mod_cast BSD_ap_p4759
  have key : r ^ 2 - (a_p 4759 : ℝ) * r + ((4759 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 18252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

-- p=4783: a_p=+51, 4p-a_p²=16531
theorem BSD_DegreeNonneg_p4783 : BSD_FrobeniusDegreeNonneg_OPEN 4783 := fun r => by
  have hap : (a_p 4783 : ℝ) = 51 := by exact_mod_cast BSD_ap_p4783
  have key : r ^ 2 - (a_p 4783 : ℝ) * r + ((4783 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 16531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

-- p=4787: a_p=-28, 4p-a_p²=18364
theorem BSD_DegreeNonneg_p4787 : BSD_FrobeniusDegreeNonneg_OPEN 4787 := fun r => by
  have hap : (a_p 4787 : ℝ) = -28 := by exact_mod_cast BSD_ap_p4787
  have key : r ^ 2 - (a_p 4787 : ℝ) * r + ((4787 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 18364/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

-- p=4789: a_p=-86, 4p-a_p²=11760
theorem BSD_DegreeNonneg_p4789 : BSD_FrobeniusDegreeNonneg_OPEN 4789 := fun r => by
  have hap : (a_p 4789 : ℝ) = -86 := by exact_mod_cast BSD_ap_p4789
  have key : r ^ 2 - (a_p 4789 : ℝ) * r + ((4789 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 11760/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

-- p=4793: a_p=-58, 4p-a_p²=15808
theorem BSD_DegreeNonneg_p4793 : BSD_FrobeniusDegreeNonneg_OPEN 4793 := fun r => by
  have hap : (a_p 4793 : ℝ) = -58 := by exact_mod_cast BSD_ap_p4793
  have key : r ^ 2 - (a_p 4793 : ℝ) * r + ((4793 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 15808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=4799: a_p=+47, 4p-a_p²=16987
theorem BSD_DegreeNonneg_p4799 : BSD_FrobeniusDegreeNonneg_OPEN 4799 := fun r => by
  have hap : (a_p 4799 : ℝ) = 47 := by exact_mod_cast BSD_ap_p4799
  have key : r ^ 2 - (a_p 4799 : ℝ) * r + ((4799 : ℕ) : ℝ) =
      (r - 47/2) ^ 2 + 16987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (47 : ℝ)/2)]

-- p=4801: a_p=-75, 4p-a_p²=13579
theorem BSD_DegreeNonneg_p4801 : BSD_FrobeniusDegreeNonneg_OPEN 4801 := fun r => by
  have hap : (a_p 4801 : ℝ) = -75 := by exact_mod_cast BSD_ap_p4801
  have key : r ^ 2 - (a_p 4801 : ℝ) * r + ((4801 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 13579/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

-- p=4813: a_p=-84, 4p-a_p²=12196
theorem BSD_DegreeNonneg_p4813 : BSD_FrobeniusDegreeNonneg_OPEN 4813 := fun r => by
  have hap : (a_p 4813 : ℝ) = -84 := by exact_mod_cast BSD_ap_p4813
  have key : r ^ 2 - (a_p 4813 : ℝ) * r + ((4813 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 12196/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4733 : BSD_Hasse_OPEN 4733 :=
  BSD_hasse_of_degree_nonneg 4733 BSD_DegreeNonneg_p4733
theorem BSD_Hasse_OPEN_p4751 : BSD_Hasse_OPEN 4751 :=
  BSD_hasse_of_degree_nonneg 4751 BSD_DegreeNonneg_p4751
theorem BSD_Hasse_OPEN_p4759 : BSD_Hasse_OPEN 4759 :=
  BSD_hasse_of_degree_nonneg 4759 BSD_DegreeNonneg_p4759
theorem BSD_Hasse_OPEN_p4783 : BSD_Hasse_OPEN 4783 :=
  BSD_hasse_of_degree_nonneg 4783 BSD_DegreeNonneg_p4783
theorem BSD_Hasse_OPEN_p4787 : BSD_Hasse_OPEN 4787 :=
  BSD_hasse_of_degree_nonneg 4787 BSD_DegreeNonneg_p4787
theorem BSD_Hasse_OPEN_p4789 : BSD_Hasse_OPEN 4789 :=
  BSD_hasse_of_degree_nonneg 4789 BSD_DegreeNonneg_p4789
theorem BSD_Hasse_OPEN_p4793 : BSD_Hasse_OPEN 4793 :=
  BSD_hasse_of_degree_nonneg 4793 BSD_DegreeNonneg_p4793
theorem BSD_Hasse_OPEN_p4799 : BSD_Hasse_OPEN 4799 :=
  BSD_hasse_of_degree_nonneg 4799 BSD_DegreeNonneg_p4799
theorem BSD_Hasse_OPEN_p4801 : BSD_Hasse_OPEN 4801 :=
  BSD_hasse_of_degree_nonneg 4801 BSD_DegreeNonneg_p4801
theorem BSD_Hasse_OPEN_p4813 : BSD_Hasse_OPEN 4813 :=
  BSD_hasse_of_degree_nonneg 4813 BSD_DegreeNonneg_p4813

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4733 : (a_p 4733 : ℝ) ^ 2 ≤ 4 * (4733 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4733
theorem BSD_HasseBound_Disc_p4751 : (a_p 4751 : ℝ) ^ 2 ≤ 4 * (4751 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4751
theorem BSD_HasseBound_Disc_p4759 : (a_p 4759 : ℝ) ^ 2 ≤ 4 * (4759 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4759
theorem BSD_HasseBound_Disc_p4783 : (a_p 4783 : ℝ) ^ 2 ≤ 4 * (4783 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4783
theorem BSD_HasseBound_Disc_p4787 : (a_p 4787 : ℝ) ^ 2 ≤ 4 * (4787 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4787
theorem BSD_HasseBound_Disc_p4789 : (a_p 4789 : ℝ) ^ 2 ≤ 4 * (4789 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4789
theorem BSD_HasseBound_Disc_p4793 : (a_p 4793 : ℝ) ^ 2 ≤ 4 * (4793 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4793
theorem BSD_HasseBound_Disc_p4799 : (a_p 4799 : ℝ) ^ 2 ≤ 4 * (4799 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4799
theorem BSD_HasseBound_Disc_p4801 : (a_p 4801 : ℝ) ^ 2 ≤ 4 * (4801 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4801
theorem BSD_HasseBound_Disc_p4813 : (a_p 4813 : ℝ) ^ 2 ≤ 4 * (4813 : ℝ) :=
  BSD_disc_from_deg_830 BSD_DegreeNonneg_p4813

end Towers.BSD