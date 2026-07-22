/-
================================================================
Towers / BSD / BSD_Genesis806_CLOSED  (genesis-806)

HasseBridge Tier C: Hasse bounds for primes
2731..2801 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2731: card=2800, a_p=-68, disc=-6300
  p=2741: card=2720, a_p=+22, disc=-10480
  p=2749: card=2724, a_p=+26, disc=-10320
  p=2753: card=2733, a_p=+21, disc=-10571
  p=2767: card=2838, a_p=-70, disc=-6168
  p=2777: card=2704, a_p=+74, disc=-5632
  p=2789: card=2884, a_p=-94, disc=-2320
  p=2791: card=2860, a_p=-68, disc=-6540
  p=2797: card=2828, a_p=-30, disc=-10288
  p=2801: card=2794, a_p=+8, disc=-11140

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_806 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i806_p2731 : Fact (2731 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2741 : Fact (2741 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2749 : Fact (2749 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2753 : Fact (2753 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2767 : Fact (2767 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2777 : Fact (2777 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2789 : Fact (2789 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2791 : Fact (2791 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2797 : Fact (2797 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2801 : Fact (2801 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2731 : (E143_Finset 2731).card = 2800 := by native_decide
theorem BSD_E143_card_p2741 : (E143_Finset 2741).card = 2720 := by native_decide
theorem BSD_E143_card_p2749 : (E143_Finset 2749).card = 2724 := by native_decide
theorem BSD_E143_card_p2753 : (E143_Finset 2753).card = 2733 := by native_decide
theorem BSD_E143_card_p2767 : (E143_Finset 2767).card = 2838 := by native_decide
theorem BSD_E143_card_p2777 : (E143_Finset 2777).card = 2704 := by native_decide
theorem BSD_E143_card_p2789 : (E143_Finset 2789).card = 2884 := by native_decide
theorem BSD_E143_card_p2791 : (E143_Finset 2791).card = 2860 := by native_decide
theorem BSD_E143_card_p2797 : (E143_Finset 2797).card = 2828 := by native_decide
theorem BSD_E143_card_p2801 : (E143_Finset 2801).card = 2794 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2731 : a_p 2731 = (-68 : ℤ) := by
  have h := BSD_E143_card_p2731; unfold a_p; omega
theorem BSD_ap_p2741 : a_p 2741 = (22 : ℤ) := by
  have h := BSD_E143_card_p2741; unfold a_p; omega
theorem BSD_ap_p2749 : a_p 2749 = (26 : ℤ) := by
  have h := BSD_E143_card_p2749; unfold a_p; omega
theorem BSD_ap_p2753 : a_p 2753 = (21 : ℤ) := by
  have h := BSD_E143_card_p2753; unfold a_p; omega
theorem BSD_ap_p2767 : a_p 2767 = (-70 : ℤ) := by
  have h := BSD_E143_card_p2767; unfold a_p; omega
theorem BSD_ap_p2777 : a_p 2777 = (74 : ℤ) := by
  have h := BSD_E143_card_p2777; unfold a_p; omega
theorem BSD_ap_p2789 : a_p 2789 = (-94 : ℤ) := by
  have h := BSD_E143_card_p2789; unfold a_p; omega
theorem BSD_ap_p2791 : a_p 2791 = (-68 : ℤ) := by
  have h := BSD_E143_card_p2791; unfold a_p; omega
theorem BSD_ap_p2797 : a_p 2797 = (-30 : ℤ) := by
  have h := BSD_E143_card_p2797; unfold a_p; omega
theorem BSD_ap_p2801 : a_p 2801 = (8 : ℤ) := by
  have h := BSD_E143_card_p2801; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2731: a_p=-68, 4p-a_p²=6300
theorem BSD_DegreeNonneg_p2731 : BSD_FrobeniusDegreeNonneg_OPEN 2731 := fun r => by
  have hap : (a_p 2731 : ℝ) = -68 := by exact_mod_cast BSD_ap_p2731
  have key : r ^ 2 - (a_p 2731 : ℝ) * r + ((2731 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 6300/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

-- p=2741: a_p=+22, 4p-a_p²=10480
theorem BSD_DegreeNonneg_p2741 : BSD_FrobeniusDegreeNonneg_OPEN 2741 := fun r => by
  have hap : (a_p 2741 : ℝ) = 22 := by exact_mod_cast BSD_ap_p2741
  have key : r ^ 2 - (a_p 2741 : ℝ) * r + ((2741 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 10480/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

-- p=2749: a_p=+26, 4p-a_p²=10320
theorem BSD_DegreeNonneg_p2749 : BSD_FrobeniusDegreeNonneg_OPEN 2749 := fun r => by
  have hap : (a_p 2749 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2749
  have key : r ^ 2 - (a_p 2749 : ℝ) * r + ((2749 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 10320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

-- p=2753: a_p=+21, 4p-a_p²=10571
theorem BSD_DegreeNonneg_p2753 : BSD_FrobeniusDegreeNonneg_OPEN 2753 := fun r => by
  have hap : (a_p 2753 : ℝ) = 21 := by exact_mod_cast BSD_ap_p2753
  have key : r ^ 2 - (a_p 2753 : ℝ) * r + ((2753 : ℕ) : ℝ) =
      (r - 21/2) ^ 2 + 10571/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (21 : ℝ)/2)]

-- p=2767: a_p=-70, 4p-a_p²=6168
theorem BSD_DegreeNonneg_p2767 : BSD_FrobeniusDegreeNonneg_OPEN 2767 := fun r => by
  have hap : (a_p 2767 : ℝ) = -70 := by exact_mod_cast BSD_ap_p2767
  have key : r ^ 2 - (a_p 2767 : ℝ) * r + ((2767 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 6168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

-- p=2777: a_p=+74, 4p-a_p²=5632
theorem BSD_DegreeNonneg_p2777 : BSD_FrobeniusDegreeNonneg_OPEN 2777 := fun r => by
  have hap : (a_p 2777 : ℝ) = 74 := by exact_mod_cast BSD_ap_p2777
  have key : r ^ 2 - (a_p 2777 : ℝ) * r + ((2777 : ℕ) : ℝ) =
      (r - 74/2) ^ 2 + 5632/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (74 : ℝ)/2)]

-- p=2789: a_p=-94, 4p-a_p²=2320
theorem BSD_DegreeNonneg_p2789 : BSD_FrobeniusDegreeNonneg_OPEN 2789 := fun r => by
  have hap : (a_p 2789 : ℝ) = -94 := by exact_mod_cast BSD_ap_p2789
  have key : r ^ 2 - (a_p 2789 : ℝ) * r + ((2789 : ℕ) : ℝ) =
      (r + 94/2) ^ 2 + 2320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (94 : ℝ)/2)]

-- p=2791: a_p=-68, 4p-a_p²=6540
theorem BSD_DegreeNonneg_p2791 : BSD_FrobeniusDegreeNonneg_OPEN 2791 := fun r => by
  have hap : (a_p 2791 : ℝ) = -68 := by exact_mod_cast BSD_ap_p2791
  have key : r ^ 2 - (a_p 2791 : ℝ) * r + ((2791 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 6540/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

-- p=2797: a_p=-30, 4p-a_p²=10288
theorem BSD_DegreeNonneg_p2797 : BSD_FrobeniusDegreeNonneg_OPEN 2797 := fun r => by
  have hap : (a_p 2797 : ℝ) = -30 := by exact_mod_cast BSD_ap_p2797
  have key : r ^ 2 - (a_p 2797 : ℝ) * r + ((2797 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 10288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

-- p=2801: a_p=+8, 4p-a_p²=11140
theorem BSD_DegreeNonneg_p2801 : BSD_FrobeniusDegreeNonneg_OPEN 2801 := fun r => by
  have hap : (a_p 2801 : ℝ) = 8 := by exact_mod_cast BSD_ap_p2801
  have key : r ^ 2 - (a_p 2801 : ℝ) * r + ((2801 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 11140/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2731 : BSD_Hasse_OPEN 2731 :=
  BSD_hasse_of_degree_nonneg 2731 BSD_DegreeNonneg_p2731
theorem BSD_Hasse_OPEN_p2741 : BSD_Hasse_OPEN 2741 :=
  BSD_hasse_of_degree_nonneg 2741 BSD_DegreeNonneg_p2741
theorem BSD_Hasse_OPEN_p2749 : BSD_Hasse_OPEN 2749 :=
  BSD_hasse_of_degree_nonneg 2749 BSD_DegreeNonneg_p2749
theorem BSD_Hasse_OPEN_p2753 : BSD_Hasse_OPEN 2753 :=
  BSD_hasse_of_degree_nonneg 2753 BSD_DegreeNonneg_p2753
theorem BSD_Hasse_OPEN_p2767 : BSD_Hasse_OPEN 2767 :=
  BSD_hasse_of_degree_nonneg 2767 BSD_DegreeNonneg_p2767
theorem BSD_Hasse_OPEN_p2777 : BSD_Hasse_OPEN 2777 :=
  BSD_hasse_of_degree_nonneg 2777 BSD_DegreeNonneg_p2777
theorem BSD_Hasse_OPEN_p2789 : BSD_Hasse_OPEN 2789 :=
  BSD_hasse_of_degree_nonneg 2789 BSD_DegreeNonneg_p2789
theorem BSD_Hasse_OPEN_p2791 : BSD_Hasse_OPEN 2791 :=
  BSD_hasse_of_degree_nonneg 2791 BSD_DegreeNonneg_p2791
theorem BSD_Hasse_OPEN_p2797 : BSD_Hasse_OPEN 2797 :=
  BSD_hasse_of_degree_nonneg 2797 BSD_DegreeNonneg_p2797
theorem BSD_Hasse_OPEN_p2801 : BSD_Hasse_OPEN 2801 :=
  BSD_hasse_of_degree_nonneg 2801 BSD_DegreeNonneg_p2801

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2731 : (a_p 2731 : ℝ) ^ 2 ≤ 4 * (2731 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2731
theorem BSD_HasseBound_Disc_p2741 : (a_p 2741 : ℝ) ^ 2 ≤ 4 * (2741 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2741
theorem BSD_HasseBound_Disc_p2749 : (a_p 2749 : ℝ) ^ 2 ≤ 4 * (2749 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2749
theorem BSD_HasseBound_Disc_p2753 : (a_p 2753 : ℝ) ^ 2 ≤ 4 * (2753 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2753
theorem BSD_HasseBound_Disc_p2767 : (a_p 2767 : ℝ) ^ 2 ≤ 4 * (2767 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2767
theorem BSD_HasseBound_Disc_p2777 : (a_p 2777 : ℝ) ^ 2 ≤ 4 * (2777 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2777
theorem BSD_HasseBound_Disc_p2789 : (a_p 2789 : ℝ) ^ 2 ≤ 4 * (2789 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2789
theorem BSD_HasseBound_Disc_p2791 : (a_p 2791 : ℝ) ^ 2 ≤ 4 * (2791 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2791
theorem BSD_HasseBound_Disc_p2797 : (a_p 2797 : ℝ) ^ 2 ≤ 4 * (2797 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2797
theorem BSD_HasseBound_Disc_p2801 : (a_p 2801 : ℝ) ^ 2 ≤ 4 * (2801 : ℝ) :=
  BSD_disc_from_deg_806 BSD_DegreeNonneg_p2801

end Towers.BSD