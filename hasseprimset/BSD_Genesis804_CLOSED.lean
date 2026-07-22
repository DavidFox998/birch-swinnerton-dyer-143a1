/-
================================================================
Towers / BSD / BSD_Genesis804_CLOSED  (genesis-804)

HasseBridge Tier C: Hasse bounds for primes
2609..2677 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2609: card=2530, a_p=+80, disc=-4036
  p=2617: card=2636, a_p=-18, disc=-10144
  p=2621: card=2700, a_p=-78, disc=-4400
  p=2633: card=2661, a_p=-27, disc=-9803
  p=2647: card=2696, a_p=-48, disc=-8284
  p=2657: card=2592, a_p=+66, disc=-6272
  p=2659: card=2612, a_p=+48, disc=-8332
  p=2663: card=2723, a_p=-59, disc=-7171
  p=2671: card=2720, a_p=-48, disc=-8380
  p=2677: card=2601, a_p=+77, disc=-4779

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_804 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i804_p2609 : Fact (2609 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2617 : Fact (2617 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2621 : Fact (2621 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2633 : Fact (2633 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2647 : Fact (2647 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2657 : Fact (2657 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2659 : Fact (2659 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2663 : Fact (2663 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2671 : Fact (2671 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2677 : Fact (2677 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2609 : (E143_Finset 2609).card = 2530 := by native_decide
theorem BSD_E143_card_p2617 : (E143_Finset 2617).card = 2636 := by native_decide
theorem BSD_E143_card_p2621 : (E143_Finset 2621).card = 2700 := by native_decide
theorem BSD_E143_card_p2633 : (E143_Finset 2633).card = 2661 := by native_decide
theorem BSD_E143_card_p2647 : (E143_Finset 2647).card = 2696 := by native_decide
theorem BSD_E143_card_p2657 : (E143_Finset 2657).card = 2592 := by native_decide
theorem BSD_E143_card_p2659 : (E143_Finset 2659).card = 2612 := by native_decide
theorem BSD_E143_card_p2663 : (E143_Finset 2663).card = 2723 := by native_decide
theorem BSD_E143_card_p2671 : (E143_Finset 2671).card = 2720 := by native_decide
theorem BSD_E143_card_p2677 : (E143_Finset 2677).card = 2601 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2609 : a_p 2609 = (80 : ℤ) := by
  have h := BSD_E143_card_p2609; unfold a_p; omega
theorem BSD_ap_p2617 : a_p 2617 = (-18 : ℤ) := by
  have h := BSD_E143_card_p2617; unfold a_p; omega
theorem BSD_ap_p2621 : a_p 2621 = (-78 : ℤ) := by
  have h := BSD_E143_card_p2621; unfold a_p; omega
theorem BSD_ap_p2633 : a_p 2633 = (-27 : ℤ) := by
  have h := BSD_E143_card_p2633; unfold a_p; omega
theorem BSD_ap_p2647 : a_p 2647 = (-48 : ℤ) := by
  have h := BSD_E143_card_p2647; unfold a_p; omega
theorem BSD_ap_p2657 : a_p 2657 = (66 : ℤ) := by
  have h := BSD_E143_card_p2657; unfold a_p; omega
theorem BSD_ap_p2659 : a_p 2659 = (48 : ℤ) := by
  have h := BSD_E143_card_p2659; unfold a_p; omega
theorem BSD_ap_p2663 : a_p 2663 = (-59 : ℤ) := by
  have h := BSD_E143_card_p2663; unfold a_p; omega
theorem BSD_ap_p2671 : a_p 2671 = (-48 : ℤ) := by
  have h := BSD_E143_card_p2671; unfold a_p; omega
theorem BSD_ap_p2677 : a_p 2677 = (77 : ℤ) := by
  have h := BSD_E143_card_p2677; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2609: a_p=+80, 4p-a_p²=4036
theorem BSD_DegreeNonneg_p2609 : BSD_FrobeniusDegreeNonneg_OPEN 2609 := fun r => by
  have hap : (a_p 2609 : ℝ) = 80 := by exact_mod_cast BSD_ap_p2609
  have key : r ^ 2 - (a_p 2609 : ℝ) * r + ((2609 : ℕ) : ℝ) =
      (r - 80/2) ^ 2 + 4036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (80 : ℝ)/2)]

-- p=2617: a_p=-18, 4p-a_p²=10144
theorem BSD_DegreeNonneg_p2617 : BSD_FrobeniusDegreeNonneg_OPEN 2617 := fun r => by
  have hap : (a_p 2617 : ℝ) = -18 := by exact_mod_cast BSD_ap_p2617
  have key : r ^ 2 - (a_p 2617 : ℝ) * r + ((2617 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 10144/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

-- p=2621: a_p=-78, 4p-a_p²=4400
theorem BSD_DegreeNonneg_p2621 : BSD_FrobeniusDegreeNonneg_OPEN 2621 := fun r => by
  have hap : (a_p 2621 : ℝ) = -78 := by exact_mod_cast BSD_ap_p2621
  have key : r ^ 2 - (a_p 2621 : ℝ) * r + ((2621 : ℕ) : ℝ) =
      (r + 78/2) ^ 2 + 4400/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (78 : ℝ)/2)]

-- p=2633: a_p=-27, 4p-a_p²=9803
theorem BSD_DegreeNonneg_p2633 : BSD_FrobeniusDegreeNonneg_OPEN 2633 := fun r => by
  have hap : (a_p 2633 : ℝ) = -27 := by exact_mod_cast BSD_ap_p2633
  have key : r ^ 2 - (a_p 2633 : ℝ) * r + ((2633 : ℕ) : ℝ) =
      (r + 27/2) ^ 2 + 9803/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (27 : ℝ)/2)]

-- p=2647: a_p=-48, 4p-a_p²=8284
theorem BSD_DegreeNonneg_p2647 : BSD_FrobeniusDegreeNonneg_OPEN 2647 := fun r => by
  have hap : (a_p 2647 : ℝ) = -48 := by exact_mod_cast BSD_ap_p2647
  have key : r ^ 2 - (a_p 2647 : ℝ) * r + ((2647 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 8284/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

-- p=2657: a_p=+66, 4p-a_p²=6272
theorem BSD_DegreeNonneg_p2657 : BSD_FrobeniusDegreeNonneg_OPEN 2657 := fun r => by
  have hap : (a_p 2657 : ℝ) = 66 := by exact_mod_cast BSD_ap_p2657
  have key : r ^ 2 - (a_p 2657 : ℝ) * r + ((2657 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 6272/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

-- p=2659: a_p=+48, 4p-a_p²=8332
theorem BSD_DegreeNonneg_p2659 : BSD_FrobeniusDegreeNonneg_OPEN 2659 := fun r => by
  have hap : (a_p 2659 : ℝ) = 48 := by exact_mod_cast BSD_ap_p2659
  have key : r ^ 2 - (a_p 2659 : ℝ) * r + ((2659 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 8332/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

-- p=2663: a_p=-59, 4p-a_p²=7171
theorem BSD_DegreeNonneg_p2663 : BSD_FrobeniusDegreeNonneg_OPEN 2663 := fun r => by
  have hap : (a_p 2663 : ℝ) = -59 := by exact_mod_cast BSD_ap_p2663
  have key : r ^ 2 - (a_p 2663 : ℝ) * r + ((2663 : ℕ) : ℝ) =
      (r + 59/2) ^ 2 + 7171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (59 : ℝ)/2)]

-- p=2671: a_p=-48, 4p-a_p²=8380
theorem BSD_DegreeNonneg_p2671 : BSD_FrobeniusDegreeNonneg_OPEN 2671 := fun r => by
  have hap : (a_p 2671 : ℝ) = -48 := by exact_mod_cast BSD_ap_p2671
  have key : r ^ 2 - (a_p 2671 : ℝ) * r + ((2671 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 8380/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

-- p=2677: a_p=+77, 4p-a_p²=4779
theorem BSD_DegreeNonneg_p2677 : BSD_FrobeniusDegreeNonneg_OPEN 2677 := fun r => by
  have hap : (a_p 2677 : ℝ) = 77 := by exact_mod_cast BSD_ap_p2677
  have key : r ^ 2 - (a_p 2677 : ℝ) * r + ((2677 : ℕ) : ℝ) =
      (r - 77/2) ^ 2 + 4779/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (77 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2609 : BSD_Hasse_OPEN 2609 :=
  BSD_hasse_of_degree_nonneg 2609 BSD_DegreeNonneg_p2609
theorem BSD_Hasse_OPEN_p2617 : BSD_Hasse_OPEN 2617 :=
  BSD_hasse_of_degree_nonneg 2617 BSD_DegreeNonneg_p2617
theorem BSD_Hasse_OPEN_p2621 : BSD_Hasse_OPEN 2621 :=
  BSD_hasse_of_degree_nonneg 2621 BSD_DegreeNonneg_p2621
theorem BSD_Hasse_OPEN_p2633 : BSD_Hasse_OPEN 2633 :=
  BSD_hasse_of_degree_nonneg 2633 BSD_DegreeNonneg_p2633
theorem BSD_Hasse_OPEN_p2647 : BSD_Hasse_OPEN 2647 :=
  BSD_hasse_of_degree_nonneg 2647 BSD_DegreeNonneg_p2647
theorem BSD_Hasse_OPEN_p2657 : BSD_Hasse_OPEN 2657 :=
  BSD_hasse_of_degree_nonneg 2657 BSD_DegreeNonneg_p2657
theorem BSD_Hasse_OPEN_p2659 : BSD_Hasse_OPEN 2659 :=
  BSD_hasse_of_degree_nonneg 2659 BSD_DegreeNonneg_p2659
theorem BSD_Hasse_OPEN_p2663 : BSD_Hasse_OPEN 2663 :=
  BSD_hasse_of_degree_nonneg 2663 BSD_DegreeNonneg_p2663
theorem BSD_Hasse_OPEN_p2671 : BSD_Hasse_OPEN 2671 :=
  BSD_hasse_of_degree_nonneg 2671 BSD_DegreeNonneg_p2671
theorem BSD_Hasse_OPEN_p2677 : BSD_Hasse_OPEN 2677 :=
  BSD_hasse_of_degree_nonneg 2677 BSD_DegreeNonneg_p2677

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2609 : (a_p 2609 : ℝ) ^ 2 ≤ 4 * (2609 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2609
theorem BSD_HasseBound_Disc_p2617 : (a_p 2617 : ℝ) ^ 2 ≤ 4 * (2617 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2617
theorem BSD_HasseBound_Disc_p2621 : (a_p 2621 : ℝ) ^ 2 ≤ 4 * (2621 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2621
theorem BSD_HasseBound_Disc_p2633 : (a_p 2633 : ℝ) ^ 2 ≤ 4 * (2633 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2633
theorem BSD_HasseBound_Disc_p2647 : (a_p 2647 : ℝ) ^ 2 ≤ 4 * (2647 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2647
theorem BSD_HasseBound_Disc_p2657 : (a_p 2657 : ℝ) ^ 2 ≤ 4 * (2657 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2657
theorem BSD_HasseBound_Disc_p2659 : (a_p 2659 : ℝ) ^ 2 ≤ 4 * (2659 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2659
theorem BSD_HasseBound_Disc_p2663 : (a_p 2663 : ℝ) ^ 2 ≤ 4 * (2663 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2663
theorem BSD_HasseBound_Disc_p2671 : (a_p 2671 : ℝ) ^ 2 ≤ 4 * (2671 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2671
theorem BSD_HasseBound_Disc_p2677 : (a_p 2677 : ℝ) ^ 2 ≤ 4 * (2677 : ℝ) :=
  BSD_disc_from_deg_804 BSD_DegreeNonneg_p2677

end Towers.BSD