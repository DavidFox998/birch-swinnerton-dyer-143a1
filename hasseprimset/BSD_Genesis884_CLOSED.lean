/-
================================================================
Towers / BSD / BSD_Genesis884_CLOSED  (genesis-884)

HasseBridge Tier C: Hasse bounds for primes
9521..9623 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9521: card=9572, a_p=-50, disc=-35584
  p=9533: card=9460, a_p=+74, disc=-32656
  p=9539: card=9540, a_p=+0, disc=-38156
  p=9547: card=9450, a_p=+98, disc=-28584
  p=9551: card=9413, a_p=+139, disc=-18883
  p=9587: card=9648, a_p=-60, disc=-34748
  p=9601: card=9713, a_p=-111, disc=-26083
  p=9613: card=9708, a_p=-94, disc=-29616
  p=9619: card=9548, a_p=+72, disc=-33292
  p=9623: card=9561, a_p=+63, disc=-34523

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_884 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i884_p9521 : Fact (9521 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9533 : Fact (9533 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9539 : Fact (9539 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9547 : Fact (9547 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9551 : Fact (9551 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9587 : Fact (9587 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9601 : Fact (9601 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9613 : Fact (9613 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9619 : Fact (9619 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9623 : Fact (9623 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9521 : (E143_Finset 9521).card = 9572 := by native_decide
theorem BSD_E143_card_p9533 : (E143_Finset 9533).card = 9460 := by native_decide
theorem BSD_E143_card_p9539 : (E143_Finset 9539).card = 9540 := by native_decide
theorem BSD_E143_card_p9547 : (E143_Finset 9547).card = 9450 := by native_decide
theorem BSD_E143_card_p9551 : (E143_Finset 9551).card = 9413 := by native_decide
theorem BSD_E143_card_p9587 : (E143_Finset 9587).card = 9648 := by native_decide
theorem BSD_E143_card_p9601 : (E143_Finset 9601).card = 9713 := by native_decide
theorem BSD_E143_card_p9613 : (E143_Finset 9613).card = 9708 := by native_decide
theorem BSD_E143_card_p9619 : (E143_Finset 9619).card = 9548 := by native_decide
theorem BSD_E143_card_p9623 : (E143_Finset 9623).card = 9561 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9521 : a_p 9521 = (-50 : ℤ) := by
  have h := BSD_E143_card_p9521; unfold a_p; omega
theorem BSD_ap_p9533 : a_p 9533 = (74 : ℤ) := by
  have h := BSD_E143_card_p9533; unfold a_p; omega
theorem BSD_ap_p9539 : a_p 9539 = (0 : ℤ) := by
  have h := BSD_E143_card_p9539; unfold a_p; omega
theorem BSD_ap_p9547 : a_p 9547 = (98 : ℤ) := by
  have h := BSD_E143_card_p9547; unfold a_p; omega
theorem BSD_ap_p9551 : a_p 9551 = (139 : ℤ) := by
  have h := BSD_E143_card_p9551; unfold a_p; omega
theorem BSD_ap_p9587 : a_p 9587 = (-60 : ℤ) := by
  have h := BSD_E143_card_p9587; unfold a_p; omega
theorem BSD_ap_p9601 : a_p 9601 = (-111 : ℤ) := by
  have h := BSD_E143_card_p9601; unfold a_p; omega
theorem BSD_ap_p9613 : a_p 9613 = (-94 : ℤ) := by
  have h := BSD_E143_card_p9613; unfold a_p; omega
theorem BSD_ap_p9619 : a_p 9619 = (72 : ℤ) := by
  have h := BSD_E143_card_p9619; unfold a_p; omega
theorem BSD_ap_p9623 : a_p 9623 = (63 : ℤ) := by
  have h := BSD_E143_card_p9623; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9521: a_p=-50, 4p-a_p²=35584
theorem BSD_DegreeNonneg_p9521 : BSD_FrobeniusDegreeNonneg_OPEN 9521 := fun r => by
  have hap : (a_p 9521 : ℝ) = -50 := by exact_mod_cast BSD_ap_p9521
  have key : r ^ 2 - (a_p 9521 : ℝ) * r + ((9521 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 35584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

-- p=9533: a_p=+74, 4p-a_p²=32656
theorem BSD_DegreeNonneg_p9533 : BSD_FrobeniusDegreeNonneg_OPEN 9533 := fun r => by
  have hap : (a_p 9533 : ℝ) = 74 := by exact_mod_cast BSD_ap_p9533
  have key : r ^ 2 - (a_p 9533 : ℝ) * r + ((9533 : ℕ) : ℝ) =
      (r - 74/2) ^ 2 + 32656/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (74 : ℝ)/2)]

-- p=9539: a_p=+0, 4p-a_p²=38156
theorem BSD_DegreeNonneg_p9539 : BSD_FrobeniusDegreeNonneg_OPEN 9539 := fun r => by
  have hap : (a_p 9539 : ℝ) = 0 := by exact_mod_cast BSD_ap_p9539
  have key : r ^ 2 - (a_p 9539 : ℝ) * r + ((9539 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 38156/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=9547: a_p=+98, 4p-a_p²=28584
theorem BSD_DegreeNonneg_p9547 : BSD_FrobeniusDegreeNonneg_OPEN 9547 := fun r => by
  have hap : (a_p 9547 : ℝ) = 98 := by exact_mod_cast BSD_ap_p9547
  have key : r ^ 2 - (a_p 9547 : ℝ) * r + ((9547 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 28584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

-- p=9551: a_p=+139, 4p-a_p²=18883
theorem BSD_DegreeNonneg_p9551 : BSD_FrobeniusDegreeNonneg_OPEN 9551 := fun r => by
  have hap : (a_p 9551 : ℝ) = 139 := by exact_mod_cast BSD_ap_p9551
  have key : r ^ 2 - (a_p 9551 : ℝ) * r + ((9551 : ℕ) : ℝ) =
      (r - 139/2) ^ 2 + 18883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (139 : ℝ)/2)]

-- p=9587: a_p=-60, 4p-a_p²=34748
theorem BSD_DegreeNonneg_p9587 : BSD_FrobeniusDegreeNonneg_OPEN 9587 := fun r => by
  have hap : (a_p 9587 : ℝ) = -60 := by exact_mod_cast BSD_ap_p9587
  have key : r ^ 2 - (a_p 9587 : ℝ) * r + ((9587 : ℕ) : ℝ) =
      (r + 60/2) ^ 2 + 34748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (60 : ℝ)/2)]

-- p=9601: a_p=-111, 4p-a_p²=26083
theorem BSD_DegreeNonneg_p9601 : BSD_FrobeniusDegreeNonneg_OPEN 9601 := fun r => by
  have hap : (a_p 9601 : ℝ) = -111 := by exact_mod_cast BSD_ap_p9601
  have key : r ^ 2 - (a_p 9601 : ℝ) * r + ((9601 : ℕ) : ℝ) =
      (r + 111/2) ^ 2 + 26083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (111 : ℝ)/2)]

-- p=9613: a_p=-94, 4p-a_p²=29616
theorem BSD_DegreeNonneg_p9613 : BSD_FrobeniusDegreeNonneg_OPEN 9613 := fun r => by
  have hap : (a_p 9613 : ℝ) = -94 := by exact_mod_cast BSD_ap_p9613
  have key : r ^ 2 - (a_p 9613 : ℝ) * r + ((9613 : ℕ) : ℝ) =
      (r + 94/2) ^ 2 + 29616/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (94 : ℝ)/2)]

-- p=9619: a_p=+72, 4p-a_p²=33292
theorem BSD_DegreeNonneg_p9619 : BSD_FrobeniusDegreeNonneg_OPEN 9619 := fun r => by
  have hap : (a_p 9619 : ℝ) = 72 := by exact_mod_cast BSD_ap_p9619
  have key : r ^ 2 - (a_p 9619 : ℝ) * r + ((9619 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 33292/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

-- p=9623: a_p=+63, 4p-a_p²=34523
theorem BSD_DegreeNonneg_p9623 : BSD_FrobeniusDegreeNonneg_OPEN 9623 := fun r => by
  have hap : (a_p 9623 : ℝ) = 63 := by exact_mod_cast BSD_ap_p9623
  have key : r ^ 2 - (a_p 9623 : ℝ) * r + ((9623 : ℕ) : ℝ) =
      (r - 63/2) ^ 2 + 34523/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (63 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9521 : BSD_Hasse_OPEN 9521 :=
  BSD_hasse_of_degree_nonneg 9521 BSD_DegreeNonneg_p9521
theorem BSD_Hasse_OPEN_p9533 : BSD_Hasse_OPEN 9533 :=
  BSD_hasse_of_degree_nonneg 9533 BSD_DegreeNonneg_p9533
theorem BSD_Hasse_OPEN_p9539 : BSD_Hasse_OPEN 9539 :=
  BSD_hasse_of_degree_nonneg 9539 BSD_DegreeNonneg_p9539
theorem BSD_Hasse_OPEN_p9547 : BSD_Hasse_OPEN 9547 :=
  BSD_hasse_of_degree_nonneg 9547 BSD_DegreeNonneg_p9547
theorem BSD_Hasse_OPEN_p9551 : BSD_Hasse_OPEN 9551 :=
  BSD_hasse_of_degree_nonneg 9551 BSD_DegreeNonneg_p9551
theorem BSD_Hasse_OPEN_p9587 : BSD_Hasse_OPEN 9587 :=
  BSD_hasse_of_degree_nonneg 9587 BSD_DegreeNonneg_p9587
theorem BSD_Hasse_OPEN_p9601 : BSD_Hasse_OPEN 9601 :=
  BSD_hasse_of_degree_nonneg 9601 BSD_DegreeNonneg_p9601
theorem BSD_Hasse_OPEN_p9613 : BSD_Hasse_OPEN 9613 :=
  BSD_hasse_of_degree_nonneg 9613 BSD_DegreeNonneg_p9613
theorem BSD_Hasse_OPEN_p9619 : BSD_Hasse_OPEN 9619 :=
  BSD_hasse_of_degree_nonneg 9619 BSD_DegreeNonneg_p9619
theorem BSD_Hasse_OPEN_p9623 : BSD_Hasse_OPEN 9623 :=
  BSD_hasse_of_degree_nonneg 9623 BSD_DegreeNonneg_p9623

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9521 : (a_p 9521 : ℝ) ^ 2 ≤ 4 * (9521 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9521
theorem BSD_HasseBound_Disc_p9533 : (a_p 9533 : ℝ) ^ 2 ≤ 4 * (9533 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9533
theorem BSD_HasseBound_Disc_p9539 : (a_p 9539 : ℝ) ^ 2 ≤ 4 * (9539 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9539
theorem BSD_HasseBound_Disc_p9547 : (a_p 9547 : ℝ) ^ 2 ≤ 4 * (9547 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9547
theorem BSD_HasseBound_Disc_p9551 : (a_p 9551 : ℝ) ^ 2 ≤ 4 * (9551 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9551
theorem BSD_HasseBound_Disc_p9587 : (a_p 9587 : ℝ) ^ 2 ≤ 4 * (9587 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9587
theorem BSD_HasseBound_Disc_p9601 : (a_p 9601 : ℝ) ^ 2 ≤ 4 * (9601 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9601
theorem BSD_HasseBound_Disc_p9613 : (a_p 9613 : ℝ) ^ 2 ≤ 4 * (9613 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9613
theorem BSD_HasseBound_Disc_p9619 : (a_p 9619 : ℝ) ^ 2 ≤ 4 * (9619 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9619
theorem BSD_HasseBound_Disc_p9623 : (a_p 9623 : ℝ) ^ 2 ≤ 4 * (9623 : ℝ) :=
  BSD_disc_from_deg_884 BSD_DegreeNonneg_p9623

end Towers.BSD