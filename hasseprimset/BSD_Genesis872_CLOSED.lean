/-
================================================================
Towers / BSD / BSD_Genesis872_CLOSED  (genesis-872)

HasseBridge Tier C: Hasse bounds for primes
8467..8573 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8467: card=8538, a_p=-70, disc=-28968
  p=8501: card=8609, a_p=-107, disc=-22555
  p=8513: card=8598, a_p=-84, disc=-26996
  p=8521: card=8508, a_p=+14, disc=-33888
  p=8527: card=8702, a_p=-174, disc=-3832
  p=8537: card=8409, a_p=+129, disc=-17507
  p=8539: card=8625, a_p=-85, disc=-26931
  p=8543: card=8610, a_p=-66, disc=-29816
  p=8563: card=8528, a_p=+36, disc=-32956
  p=8573: card=8496, a_p=+78, disc=-28208

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_872 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i872_p8467 : Fact (8467 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8501 : Fact (8501 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8513 : Fact (8513 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8521 : Fact (8521 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8527 : Fact (8527 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8537 : Fact (8537 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8539 : Fact (8539 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8543 : Fact (8543 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8563 : Fact (8563 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8573 : Fact (8573 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8467 : (E143_Finset 8467).card = 8538 := by native_decide
theorem BSD_E143_card_p8501 : (E143_Finset 8501).card = 8609 := by native_decide
theorem BSD_E143_card_p8513 : (E143_Finset 8513).card = 8598 := by native_decide
theorem BSD_E143_card_p8521 : (E143_Finset 8521).card = 8508 := by native_decide
theorem BSD_E143_card_p8527 : (E143_Finset 8527).card = 8702 := by native_decide
theorem BSD_E143_card_p8537 : (E143_Finset 8537).card = 8409 := by native_decide
theorem BSD_E143_card_p8539 : (E143_Finset 8539).card = 8625 := by native_decide
theorem BSD_E143_card_p8543 : (E143_Finset 8543).card = 8610 := by native_decide
theorem BSD_E143_card_p8563 : (E143_Finset 8563).card = 8528 := by native_decide
theorem BSD_E143_card_p8573 : (E143_Finset 8573).card = 8496 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8467 : a_p 8467 = (-70 : ℤ) := by
  have h := BSD_E143_card_p8467; unfold a_p; omega
theorem BSD_ap_p8501 : a_p 8501 = (-107 : ℤ) := by
  have h := BSD_E143_card_p8501; unfold a_p; omega
theorem BSD_ap_p8513 : a_p 8513 = (-84 : ℤ) := by
  have h := BSD_E143_card_p8513; unfold a_p; omega
theorem BSD_ap_p8521 : a_p 8521 = (14 : ℤ) := by
  have h := BSD_E143_card_p8521; unfold a_p; omega
theorem BSD_ap_p8527 : a_p 8527 = (-174 : ℤ) := by
  have h := BSD_E143_card_p8527; unfold a_p; omega
theorem BSD_ap_p8537 : a_p 8537 = (129 : ℤ) := by
  have h := BSD_E143_card_p8537; unfold a_p; omega
theorem BSD_ap_p8539 : a_p 8539 = (-85 : ℤ) := by
  have h := BSD_E143_card_p8539; unfold a_p; omega
theorem BSD_ap_p8543 : a_p 8543 = (-66 : ℤ) := by
  have h := BSD_E143_card_p8543; unfold a_p; omega
theorem BSD_ap_p8563 : a_p 8563 = (36 : ℤ) := by
  have h := BSD_E143_card_p8563; unfold a_p; omega
theorem BSD_ap_p8573 : a_p 8573 = (78 : ℤ) := by
  have h := BSD_E143_card_p8573; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8467: a_p=-70, 4p-a_p²=28968
theorem BSD_DegreeNonneg_p8467 : BSD_FrobeniusDegreeNonneg_OPEN 8467 := fun r => by
  have hap : (a_p 8467 : ℝ) = -70 := by exact_mod_cast BSD_ap_p8467
  have key : r ^ 2 - (a_p 8467 : ℝ) * r + ((8467 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 28968/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

-- p=8501: a_p=-107, 4p-a_p²=22555
theorem BSD_DegreeNonneg_p8501 : BSD_FrobeniusDegreeNonneg_OPEN 8501 := fun r => by
  have hap : (a_p 8501 : ℝ) = -107 := by exact_mod_cast BSD_ap_p8501
  have key : r ^ 2 - (a_p 8501 : ℝ) * r + ((8501 : ℕ) : ℝ) =
      (r + 107/2) ^ 2 + 22555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (107 : ℝ)/2)]

-- p=8513: a_p=-84, 4p-a_p²=26996
theorem BSD_DegreeNonneg_p8513 : BSD_FrobeniusDegreeNonneg_OPEN 8513 := fun r => by
  have hap : (a_p 8513 : ℝ) = -84 := by exact_mod_cast BSD_ap_p8513
  have key : r ^ 2 - (a_p 8513 : ℝ) * r + ((8513 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 26996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

-- p=8521: a_p=+14, 4p-a_p²=33888
theorem BSD_DegreeNonneg_p8521 : BSD_FrobeniusDegreeNonneg_OPEN 8521 := fun r => by
  have hap : (a_p 8521 : ℝ) = 14 := by exact_mod_cast BSD_ap_p8521
  have key : r ^ 2 - (a_p 8521 : ℝ) * r + ((8521 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 33888/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

-- p=8527: a_p=-174, 4p-a_p²=3832
theorem BSD_DegreeNonneg_p8527 : BSD_FrobeniusDegreeNonneg_OPEN 8527 := fun r => by
  have hap : (a_p 8527 : ℝ) = -174 := by exact_mod_cast BSD_ap_p8527
  have key : r ^ 2 - (a_p 8527 : ℝ) * r + ((8527 : ℕ) : ℝ) =
      (r + 174/2) ^ 2 + 3832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (174 : ℝ)/2)]

-- p=8537: a_p=+129, 4p-a_p²=17507
theorem BSD_DegreeNonneg_p8537 : BSD_FrobeniusDegreeNonneg_OPEN 8537 := fun r => by
  have hap : (a_p 8537 : ℝ) = 129 := by exact_mod_cast BSD_ap_p8537
  have key : r ^ 2 - (a_p 8537 : ℝ) * r + ((8537 : ℕ) : ℝ) =
      (r - 129/2) ^ 2 + 17507/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (129 : ℝ)/2)]

-- p=8539: a_p=-85, 4p-a_p²=26931
theorem BSD_DegreeNonneg_p8539 : BSD_FrobeniusDegreeNonneg_OPEN 8539 := fun r => by
  have hap : (a_p 8539 : ℝ) = -85 := by exact_mod_cast BSD_ap_p8539
  have key : r ^ 2 - (a_p 8539 : ℝ) * r + ((8539 : ℕ) : ℝ) =
      (r + 85/2) ^ 2 + 26931/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (85 : ℝ)/2)]

-- p=8543: a_p=-66, 4p-a_p²=29816
theorem BSD_DegreeNonneg_p8543 : BSD_FrobeniusDegreeNonneg_OPEN 8543 := fun r => by
  have hap : (a_p 8543 : ℝ) = -66 := by exact_mod_cast BSD_ap_p8543
  have key : r ^ 2 - (a_p 8543 : ℝ) * r + ((8543 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 29816/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

-- p=8563: a_p=+36, 4p-a_p²=32956
theorem BSD_DegreeNonneg_p8563 : BSD_FrobeniusDegreeNonneg_OPEN 8563 := fun r => by
  have hap : (a_p 8563 : ℝ) = 36 := by exact_mod_cast BSD_ap_p8563
  have key : r ^ 2 - (a_p 8563 : ℝ) * r + ((8563 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 32956/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

-- p=8573: a_p=+78, 4p-a_p²=28208
theorem BSD_DegreeNonneg_p8573 : BSD_FrobeniusDegreeNonneg_OPEN 8573 := fun r => by
  have hap : (a_p 8573 : ℝ) = 78 := by exact_mod_cast BSD_ap_p8573
  have key : r ^ 2 - (a_p 8573 : ℝ) * r + ((8573 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 28208/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8467 : BSD_Hasse_OPEN 8467 :=
  BSD_hasse_of_degree_nonneg 8467 BSD_DegreeNonneg_p8467
theorem BSD_Hasse_OPEN_p8501 : BSD_Hasse_OPEN 8501 :=
  BSD_hasse_of_degree_nonneg 8501 BSD_DegreeNonneg_p8501
theorem BSD_Hasse_OPEN_p8513 : BSD_Hasse_OPEN 8513 :=
  BSD_hasse_of_degree_nonneg 8513 BSD_DegreeNonneg_p8513
theorem BSD_Hasse_OPEN_p8521 : BSD_Hasse_OPEN 8521 :=
  BSD_hasse_of_degree_nonneg 8521 BSD_DegreeNonneg_p8521
theorem BSD_Hasse_OPEN_p8527 : BSD_Hasse_OPEN 8527 :=
  BSD_hasse_of_degree_nonneg 8527 BSD_DegreeNonneg_p8527
theorem BSD_Hasse_OPEN_p8537 : BSD_Hasse_OPEN 8537 :=
  BSD_hasse_of_degree_nonneg 8537 BSD_DegreeNonneg_p8537
theorem BSD_Hasse_OPEN_p8539 : BSD_Hasse_OPEN 8539 :=
  BSD_hasse_of_degree_nonneg 8539 BSD_DegreeNonneg_p8539
theorem BSD_Hasse_OPEN_p8543 : BSD_Hasse_OPEN 8543 :=
  BSD_hasse_of_degree_nonneg 8543 BSD_DegreeNonneg_p8543
theorem BSD_Hasse_OPEN_p8563 : BSD_Hasse_OPEN 8563 :=
  BSD_hasse_of_degree_nonneg 8563 BSD_DegreeNonneg_p8563
theorem BSD_Hasse_OPEN_p8573 : BSD_Hasse_OPEN 8573 :=
  BSD_hasse_of_degree_nonneg 8573 BSD_DegreeNonneg_p8573

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8467 : (a_p 8467 : ℝ) ^ 2 ≤ 4 * (8467 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8467
theorem BSD_HasseBound_Disc_p8501 : (a_p 8501 : ℝ) ^ 2 ≤ 4 * (8501 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8501
theorem BSD_HasseBound_Disc_p8513 : (a_p 8513 : ℝ) ^ 2 ≤ 4 * (8513 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8513
theorem BSD_HasseBound_Disc_p8521 : (a_p 8521 : ℝ) ^ 2 ≤ 4 * (8521 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8521
theorem BSD_HasseBound_Disc_p8527 : (a_p 8527 : ℝ) ^ 2 ≤ 4 * (8527 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8527
theorem BSD_HasseBound_Disc_p8537 : (a_p 8537 : ℝ) ^ 2 ≤ 4 * (8537 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8537
theorem BSD_HasseBound_Disc_p8539 : (a_p 8539 : ℝ) ^ 2 ≤ 4 * (8539 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8539
theorem BSD_HasseBound_Disc_p8543 : (a_p 8543 : ℝ) ^ 2 ≤ 4 * (8543 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8543
theorem BSD_HasseBound_Disc_p8563 : (a_p 8563 : ℝ) ^ 2 ≤ 4 * (8563 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8563
theorem BSD_HasseBound_Disc_p8573 : (a_p 8573 : ℝ) ^ 2 ≤ 4 * (8573 : ℝ) :=
  BSD_disc_from_deg_872 BSD_DegreeNonneg_p8573

end Towers.BSD