/-
================================================================
Towers / BSD / BSD_Genesis885_CLOSED  (genesis-885)

HasseBridge Tier C: Hasse bounds for primes
9629..9719 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9629: card=9493, a_p=+137, disc=-19747
  p=9631: card=9614, a_p=+18, disc=-38200
  p=9643: card=9690, a_p=-46, disc=-36456
  p=9649: card=9678, a_p=-28, disc=-37812
  p=9661: card=9709, a_p=-47, disc=-36435
  p=9677: card=9726, a_p=-48, disc=-36404
  p=9679: card=9640, a_p=+40, disc=-37116
  p=9689: card=9705, a_p=-15, disc=-38531
  p=9697: card=9652, a_p=+46, disc=-36672
  p=9719: card=9844, a_p=-124, disc=-23500

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_885 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i885_p9629 : Fact (9629 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9631 : Fact (9631 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9643 : Fact (9643 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9649 : Fact (9649 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9661 : Fact (9661 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9677 : Fact (9677 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9679 : Fact (9679 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9689 : Fact (9689 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9697 : Fact (9697 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9719 : Fact (9719 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9629 : (E143_Finset 9629).card = 9493 := by native_decide
theorem BSD_E143_card_p9631 : (E143_Finset 9631).card = 9614 := by native_decide
theorem BSD_E143_card_p9643 : (E143_Finset 9643).card = 9690 := by native_decide
theorem BSD_E143_card_p9649 : (E143_Finset 9649).card = 9678 := by native_decide
theorem BSD_E143_card_p9661 : (E143_Finset 9661).card = 9709 := by native_decide
theorem BSD_E143_card_p9677 : (E143_Finset 9677).card = 9726 := by native_decide
theorem BSD_E143_card_p9679 : (E143_Finset 9679).card = 9640 := by native_decide
theorem BSD_E143_card_p9689 : (E143_Finset 9689).card = 9705 := by native_decide
theorem BSD_E143_card_p9697 : (E143_Finset 9697).card = 9652 := by native_decide
theorem BSD_E143_card_p9719 : (E143_Finset 9719).card = 9844 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9629 : a_p 9629 = (137 : ℤ) := by
  have h := BSD_E143_card_p9629; unfold a_p; omega
theorem BSD_ap_p9631 : a_p 9631 = (18 : ℤ) := by
  have h := BSD_E143_card_p9631; unfold a_p; omega
theorem BSD_ap_p9643 : a_p 9643 = (-46 : ℤ) := by
  have h := BSD_E143_card_p9643; unfold a_p; omega
theorem BSD_ap_p9649 : a_p 9649 = (-28 : ℤ) := by
  have h := BSD_E143_card_p9649; unfold a_p; omega
theorem BSD_ap_p9661 : a_p 9661 = (-47 : ℤ) := by
  have h := BSD_E143_card_p9661; unfold a_p; omega
theorem BSD_ap_p9677 : a_p 9677 = (-48 : ℤ) := by
  have h := BSD_E143_card_p9677; unfold a_p; omega
theorem BSD_ap_p9679 : a_p 9679 = (40 : ℤ) := by
  have h := BSD_E143_card_p9679; unfold a_p; omega
theorem BSD_ap_p9689 : a_p 9689 = (-15 : ℤ) := by
  have h := BSD_E143_card_p9689; unfold a_p; omega
theorem BSD_ap_p9697 : a_p 9697 = (46 : ℤ) := by
  have h := BSD_E143_card_p9697; unfold a_p; omega
theorem BSD_ap_p9719 : a_p 9719 = (-124 : ℤ) := by
  have h := BSD_E143_card_p9719; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9629: a_p=+137, 4p-a_p²=19747
theorem BSD_DegreeNonneg_p9629 : BSD_FrobeniusDegreeNonneg_OPEN 9629 := fun r => by
  have hap : (a_p 9629 : ℝ) = 137 := by exact_mod_cast BSD_ap_p9629
  have key : r ^ 2 - (a_p 9629 : ℝ) * r + ((9629 : ℕ) : ℝ) =
      (r - 137/2) ^ 2 + 19747/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (137 : ℝ)/2)]

-- p=9631: a_p=+18, 4p-a_p²=38200
theorem BSD_DegreeNonneg_p9631 : BSD_FrobeniusDegreeNonneg_OPEN 9631 := fun r => by
  have hap : (a_p 9631 : ℝ) = 18 := by exact_mod_cast BSD_ap_p9631
  have key : r ^ 2 - (a_p 9631 : ℝ) * r + ((9631 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 38200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=9643: a_p=-46, 4p-a_p²=36456
theorem BSD_DegreeNonneg_p9643 : BSD_FrobeniusDegreeNonneg_OPEN 9643 := fun r => by
  have hap : (a_p 9643 : ℝ) = -46 := by exact_mod_cast BSD_ap_p9643
  have key : r ^ 2 - (a_p 9643 : ℝ) * r + ((9643 : ℕ) : ℝ) =
      (r + 46/2) ^ 2 + 36456/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (46 : ℝ)/2)]

-- p=9649: a_p=-28, 4p-a_p²=37812
theorem BSD_DegreeNonneg_p9649 : BSD_FrobeniusDegreeNonneg_OPEN 9649 := fun r => by
  have hap : (a_p 9649 : ℝ) = -28 := by exact_mod_cast BSD_ap_p9649
  have key : r ^ 2 - (a_p 9649 : ℝ) * r + ((9649 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 37812/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

-- p=9661: a_p=-47, 4p-a_p²=36435
theorem BSD_DegreeNonneg_p9661 : BSD_FrobeniusDegreeNonneg_OPEN 9661 := fun r => by
  have hap : (a_p 9661 : ℝ) = -47 := by exact_mod_cast BSD_ap_p9661
  have key : r ^ 2 - (a_p 9661 : ℝ) * r + ((9661 : ℕ) : ℝ) =
      (r + 47/2) ^ 2 + 36435/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (47 : ℝ)/2)]

-- p=9677: a_p=-48, 4p-a_p²=36404
theorem BSD_DegreeNonneg_p9677 : BSD_FrobeniusDegreeNonneg_OPEN 9677 := fun r => by
  have hap : (a_p 9677 : ℝ) = -48 := by exact_mod_cast BSD_ap_p9677
  have key : r ^ 2 - (a_p 9677 : ℝ) * r + ((9677 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 36404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

-- p=9679: a_p=+40, 4p-a_p²=37116
theorem BSD_DegreeNonneg_p9679 : BSD_FrobeniusDegreeNonneg_OPEN 9679 := fun r => by
  have hap : (a_p 9679 : ℝ) = 40 := by exact_mod_cast BSD_ap_p9679
  have key : r ^ 2 - (a_p 9679 : ℝ) * r + ((9679 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 37116/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

-- p=9689: a_p=-15, 4p-a_p²=38531
theorem BSD_DegreeNonneg_p9689 : BSD_FrobeniusDegreeNonneg_OPEN 9689 := fun r => by
  have hap : (a_p 9689 : ℝ) = -15 := by exact_mod_cast BSD_ap_p9689
  have key : r ^ 2 - (a_p 9689 : ℝ) * r + ((9689 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 38531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

-- p=9697: a_p=+46, 4p-a_p²=36672
theorem BSD_DegreeNonneg_p9697 : BSD_FrobeniusDegreeNonneg_OPEN 9697 := fun r => by
  have hap : (a_p 9697 : ℝ) = 46 := by exact_mod_cast BSD_ap_p9697
  have key : r ^ 2 - (a_p 9697 : ℝ) * r + ((9697 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 36672/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=9719: a_p=-124, 4p-a_p²=23500
theorem BSD_DegreeNonneg_p9719 : BSD_FrobeniusDegreeNonneg_OPEN 9719 := fun r => by
  have hap : (a_p 9719 : ℝ) = -124 := by exact_mod_cast BSD_ap_p9719
  have key : r ^ 2 - (a_p 9719 : ℝ) * r + ((9719 : ℕ) : ℝ) =
      (r + 124/2) ^ 2 + 23500/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (124 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9629 : BSD_Hasse_OPEN 9629 :=
  BSD_hasse_of_degree_nonneg 9629 BSD_DegreeNonneg_p9629
theorem BSD_Hasse_OPEN_p9631 : BSD_Hasse_OPEN 9631 :=
  BSD_hasse_of_degree_nonneg 9631 BSD_DegreeNonneg_p9631
theorem BSD_Hasse_OPEN_p9643 : BSD_Hasse_OPEN 9643 :=
  BSD_hasse_of_degree_nonneg 9643 BSD_DegreeNonneg_p9643
theorem BSD_Hasse_OPEN_p9649 : BSD_Hasse_OPEN 9649 :=
  BSD_hasse_of_degree_nonneg 9649 BSD_DegreeNonneg_p9649
theorem BSD_Hasse_OPEN_p9661 : BSD_Hasse_OPEN 9661 :=
  BSD_hasse_of_degree_nonneg 9661 BSD_DegreeNonneg_p9661
theorem BSD_Hasse_OPEN_p9677 : BSD_Hasse_OPEN 9677 :=
  BSD_hasse_of_degree_nonneg 9677 BSD_DegreeNonneg_p9677
theorem BSD_Hasse_OPEN_p9679 : BSD_Hasse_OPEN 9679 :=
  BSD_hasse_of_degree_nonneg 9679 BSD_DegreeNonneg_p9679
theorem BSD_Hasse_OPEN_p9689 : BSD_Hasse_OPEN 9689 :=
  BSD_hasse_of_degree_nonneg 9689 BSD_DegreeNonneg_p9689
theorem BSD_Hasse_OPEN_p9697 : BSD_Hasse_OPEN 9697 :=
  BSD_hasse_of_degree_nonneg 9697 BSD_DegreeNonneg_p9697
theorem BSD_Hasse_OPEN_p9719 : BSD_Hasse_OPEN 9719 :=
  BSD_hasse_of_degree_nonneg 9719 BSD_DegreeNonneg_p9719

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9629 : (a_p 9629 : ℝ) ^ 2 ≤ 4 * (9629 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9629
theorem BSD_HasseBound_Disc_p9631 : (a_p 9631 : ℝ) ^ 2 ≤ 4 * (9631 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9631
theorem BSD_HasseBound_Disc_p9643 : (a_p 9643 : ℝ) ^ 2 ≤ 4 * (9643 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9643
theorem BSD_HasseBound_Disc_p9649 : (a_p 9649 : ℝ) ^ 2 ≤ 4 * (9649 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9649
theorem BSD_HasseBound_Disc_p9661 : (a_p 9661 : ℝ) ^ 2 ≤ 4 * (9661 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9661
theorem BSD_HasseBound_Disc_p9677 : (a_p 9677 : ℝ) ^ 2 ≤ 4 * (9677 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9677
theorem BSD_HasseBound_Disc_p9679 : (a_p 9679 : ℝ) ^ 2 ≤ 4 * (9679 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9679
theorem BSD_HasseBound_Disc_p9689 : (a_p 9689 : ℝ) ^ 2 ≤ 4 * (9689 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9689
theorem BSD_HasseBound_Disc_p9697 : (a_p 9697 : ℝ) ^ 2 ≤ 4 * (9697 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9697
theorem BSD_HasseBound_Disc_p9719 : (a_p 9719 : ℝ) ^ 2 ≤ 4 * (9719 : ℝ) :=
  BSD_disc_from_deg_885 BSD_DegreeNonneg_p9719

end Towers.BSD