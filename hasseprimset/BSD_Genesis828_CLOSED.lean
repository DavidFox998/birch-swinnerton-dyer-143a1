/-
================================================================
Towers / BSD / BSD_Genesis828_CLOSED  (genesis-828)

HasseBridge Tier C: Hasse bounds for primes
4567..4649 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4567: card=4626, a_p=-58, disc=-14904
  p=4583: card=4668, a_p=-84, disc=-11276
  p=4591: card=4712, a_p=-120, disc=-3964
  p=4597: card=4614, a_p=-16, disc=-18132
  p=4603: card=4663, a_p=-59, disc=-14931
  p=4621: card=4652, a_p=-30, disc=-17584
  p=4637: card=4674, a_p=-36, disc=-17252
  p=4639: card=4708, a_p=-68, disc=-13932
  p=4643: card=4647, a_p=-3, disc=-18563
  p=4649: card=4750, a_p=-100, disc=-8596

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_828 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i828_p4567 : Fact (4567 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4583 : Fact (4583 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4591 : Fact (4591 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4597 : Fact (4597 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4603 : Fact (4603 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4621 : Fact (4621 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4637 : Fact (4637 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4639 : Fact (4639 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4643 : Fact (4643 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4649 : Fact (4649 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4567 : (E143_Finset 4567).card = 4626 := by native_decide
theorem BSD_E143_card_p4583 : (E143_Finset 4583).card = 4668 := by native_decide
theorem BSD_E143_card_p4591 : (E143_Finset 4591).card = 4712 := by native_decide
theorem BSD_E143_card_p4597 : (E143_Finset 4597).card = 4614 := by native_decide
theorem BSD_E143_card_p4603 : (E143_Finset 4603).card = 4663 := by native_decide
theorem BSD_E143_card_p4621 : (E143_Finset 4621).card = 4652 := by native_decide
theorem BSD_E143_card_p4637 : (E143_Finset 4637).card = 4674 := by native_decide
theorem BSD_E143_card_p4639 : (E143_Finset 4639).card = 4708 := by native_decide
theorem BSD_E143_card_p4643 : (E143_Finset 4643).card = 4647 := by native_decide
theorem BSD_E143_card_p4649 : (E143_Finset 4649).card = 4750 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4567 : a_p 4567 = (-58 : ℤ) := by
  have h := BSD_E143_card_p4567; unfold a_p; omega
theorem BSD_ap_p4583 : a_p 4583 = (-84 : ℤ) := by
  have h := BSD_E143_card_p4583; unfold a_p; omega
theorem BSD_ap_p4591 : a_p 4591 = (-120 : ℤ) := by
  have h := BSD_E143_card_p4591; unfold a_p; omega
theorem BSD_ap_p4597 : a_p 4597 = (-16 : ℤ) := by
  have h := BSD_E143_card_p4597; unfold a_p; omega
theorem BSD_ap_p4603 : a_p 4603 = (-59 : ℤ) := by
  have h := BSD_E143_card_p4603; unfold a_p; omega
theorem BSD_ap_p4621 : a_p 4621 = (-30 : ℤ) := by
  have h := BSD_E143_card_p4621; unfold a_p; omega
theorem BSD_ap_p4637 : a_p 4637 = (-36 : ℤ) := by
  have h := BSD_E143_card_p4637; unfold a_p; omega
theorem BSD_ap_p4639 : a_p 4639 = (-68 : ℤ) := by
  have h := BSD_E143_card_p4639; unfold a_p; omega
theorem BSD_ap_p4643 : a_p 4643 = (-3 : ℤ) := by
  have h := BSD_E143_card_p4643; unfold a_p; omega
theorem BSD_ap_p4649 : a_p 4649 = (-100 : ℤ) := by
  have h := BSD_E143_card_p4649; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4567: a_p=-58, 4p-a_p²=14904
theorem BSD_DegreeNonneg_p4567 : BSD_FrobeniusDegreeNonneg_OPEN 4567 := fun r => by
  have hap : (a_p 4567 : ℝ) = -58 := by exact_mod_cast BSD_ap_p4567
  have key : r ^ 2 - (a_p 4567 : ℝ) * r + ((4567 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 14904/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=4583: a_p=-84, 4p-a_p²=11276
theorem BSD_DegreeNonneg_p4583 : BSD_FrobeniusDegreeNonneg_OPEN 4583 := fun r => by
  have hap : (a_p 4583 : ℝ) = -84 := by exact_mod_cast BSD_ap_p4583
  have key : r ^ 2 - (a_p 4583 : ℝ) * r + ((4583 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 11276/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

-- p=4591: a_p=-120, 4p-a_p²=3964
theorem BSD_DegreeNonneg_p4591 : BSD_FrobeniusDegreeNonneg_OPEN 4591 := fun r => by
  have hap : (a_p 4591 : ℝ) = -120 := by exact_mod_cast BSD_ap_p4591
  have key : r ^ 2 - (a_p 4591 : ℝ) * r + ((4591 : ℕ) : ℝ) =
      (r + 120/2) ^ 2 + 3964/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (120 : ℝ)/2)]

-- p=4597: a_p=-16, 4p-a_p²=18132
theorem BSD_DegreeNonneg_p4597 : BSD_FrobeniusDegreeNonneg_OPEN 4597 := fun r => by
  have hap : (a_p 4597 : ℝ) = -16 := by exact_mod_cast BSD_ap_p4597
  have key : r ^ 2 - (a_p 4597 : ℝ) * r + ((4597 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 18132/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

-- p=4603: a_p=-59, 4p-a_p²=14931
theorem BSD_DegreeNonneg_p4603 : BSD_FrobeniusDegreeNonneg_OPEN 4603 := fun r => by
  have hap : (a_p 4603 : ℝ) = -59 := by exact_mod_cast BSD_ap_p4603
  have key : r ^ 2 - (a_p 4603 : ℝ) * r + ((4603 : ℕ) : ℝ) =
      (r + 59/2) ^ 2 + 14931/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (59 : ℝ)/2)]

-- p=4621: a_p=-30, 4p-a_p²=17584
theorem BSD_DegreeNonneg_p4621 : BSD_FrobeniusDegreeNonneg_OPEN 4621 := fun r => by
  have hap : (a_p 4621 : ℝ) = -30 := by exact_mod_cast BSD_ap_p4621
  have key : r ^ 2 - (a_p 4621 : ℝ) * r + ((4621 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 17584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

-- p=4637: a_p=-36, 4p-a_p²=17252
theorem BSD_DegreeNonneg_p4637 : BSD_FrobeniusDegreeNonneg_OPEN 4637 := fun r => by
  have hap : (a_p 4637 : ℝ) = -36 := by exact_mod_cast BSD_ap_p4637
  have key : r ^ 2 - (a_p 4637 : ℝ) * r + ((4637 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 17252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

-- p=4639: a_p=-68, 4p-a_p²=13932
theorem BSD_DegreeNonneg_p4639 : BSD_FrobeniusDegreeNonneg_OPEN 4639 := fun r => by
  have hap : (a_p 4639 : ℝ) = -68 := by exact_mod_cast BSD_ap_p4639
  have key : r ^ 2 - (a_p 4639 : ℝ) * r + ((4639 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 13932/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

-- p=4643: a_p=-3, 4p-a_p²=18563
theorem BSD_DegreeNonneg_p4643 : BSD_FrobeniusDegreeNonneg_OPEN 4643 := fun r => by
  have hap : (a_p 4643 : ℝ) = -3 := by exact_mod_cast BSD_ap_p4643
  have key : r ^ 2 - (a_p 4643 : ℝ) * r + ((4643 : ℕ) : ℝ) =
      (r + 3/2) ^ 2 + 18563/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (3 : ℝ)/2)]

-- p=4649: a_p=-100, 4p-a_p²=8596
theorem BSD_DegreeNonneg_p4649 : BSD_FrobeniusDegreeNonneg_OPEN 4649 := fun r => by
  have hap : (a_p 4649 : ℝ) = -100 := by exact_mod_cast BSD_ap_p4649
  have key : r ^ 2 - (a_p 4649 : ℝ) * r + ((4649 : ℕ) : ℝ) =
      (r + 100/2) ^ 2 + 8596/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (100 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4567 : BSD_Hasse_OPEN 4567 :=
  BSD_hasse_of_degree_nonneg 4567 BSD_DegreeNonneg_p4567
theorem BSD_Hasse_OPEN_p4583 : BSD_Hasse_OPEN 4583 :=
  BSD_hasse_of_degree_nonneg 4583 BSD_DegreeNonneg_p4583
theorem BSD_Hasse_OPEN_p4591 : BSD_Hasse_OPEN 4591 :=
  BSD_hasse_of_degree_nonneg 4591 BSD_DegreeNonneg_p4591
theorem BSD_Hasse_OPEN_p4597 : BSD_Hasse_OPEN 4597 :=
  BSD_hasse_of_degree_nonneg 4597 BSD_DegreeNonneg_p4597
theorem BSD_Hasse_OPEN_p4603 : BSD_Hasse_OPEN 4603 :=
  BSD_hasse_of_degree_nonneg 4603 BSD_DegreeNonneg_p4603
theorem BSD_Hasse_OPEN_p4621 : BSD_Hasse_OPEN 4621 :=
  BSD_hasse_of_degree_nonneg 4621 BSD_DegreeNonneg_p4621
theorem BSD_Hasse_OPEN_p4637 : BSD_Hasse_OPEN 4637 :=
  BSD_hasse_of_degree_nonneg 4637 BSD_DegreeNonneg_p4637
theorem BSD_Hasse_OPEN_p4639 : BSD_Hasse_OPEN 4639 :=
  BSD_hasse_of_degree_nonneg 4639 BSD_DegreeNonneg_p4639
theorem BSD_Hasse_OPEN_p4643 : BSD_Hasse_OPEN 4643 :=
  BSD_hasse_of_degree_nonneg 4643 BSD_DegreeNonneg_p4643
theorem BSD_Hasse_OPEN_p4649 : BSD_Hasse_OPEN 4649 :=
  BSD_hasse_of_degree_nonneg 4649 BSD_DegreeNonneg_p4649

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4567 : (a_p 4567 : ℝ) ^ 2 ≤ 4 * (4567 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4567
theorem BSD_HasseBound_Disc_p4583 : (a_p 4583 : ℝ) ^ 2 ≤ 4 * (4583 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4583
theorem BSD_HasseBound_Disc_p4591 : (a_p 4591 : ℝ) ^ 2 ≤ 4 * (4591 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4591
theorem BSD_HasseBound_Disc_p4597 : (a_p 4597 : ℝ) ^ 2 ≤ 4 * (4597 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4597
theorem BSD_HasseBound_Disc_p4603 : (a_p 4603 : ℝ) ^ 2 ≤ 4 * (4603 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4603
theorem BSD_HasseBound_Disc_p4621 : (a_p 4621 : ℝ) ^ 2 ≤ 4 * (4621 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4621
theorem BSD_HasseBound_Disc_p4637 : (a_p 4637 : ℝ) ^ 2 ≤ 4 * (4637 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4637
theorem BSD_HasseBound_Disc_p4639 : (a_p 4639 : ℝ) ^ 2 ≤ 4 * (4639 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4639
theorem BSD_HasseBound_Disc_p4643 : (a_p 4643 : ℝ) ^ 2 ≤ 4 * (4643 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4643
theorem BSD_HasseBound_Disc_p4649 : (a_p 4649 : ℝ) ^ 2 ≤ 4 * (4649 : ℝ) :=
  BSD_disc_from_deg_828 BSD_DegreeNonneg_p4649

end Towers.BSD