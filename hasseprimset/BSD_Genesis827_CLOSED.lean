/-
================================================================
Towers / BSD / BSD_Genesis827_CLOSED  (genesis-827)

HasseBridge Tier C: Hasse bounds for primes
4483..4561 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4483: card=4508, a_p=-24, disc=-17356
  p=4493: card=4515, a_p=-21, disc=-17531
  p=4507: card=4534, a_p=-26, disc=-17352
  p=4513: card=4513, a_p=+1, disc=-18051
  p=4517: card=4410, a_p=+108, disc=-6404
  p=4519: card=4497, a_p=+23, disc=-17547
  p=4523: card=4456, a_p=+68, disc=-13468
  p=4547: card=4560, a_p=-12, disc=-18044
  p=4549: card=4474, a_p=+76, disc=-12420
  p=4561: card=4528, a_p=+34, disc=-17088

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_827 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i827_p4483 : Fact (4483 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4493 : Fact (4493 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4507 : Fact (4507 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4513 : Fact (4513 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4517 : Fact (4517 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4519 : Fact (4519 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4523 : Fact (4523 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4547 : Fact (4547 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4549 : Fact (4549 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4561 : Fact (4561 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4483 : (E143_Finset 4483).card = 4508 := by native_decide
theorem BSD_E143_card_p4493 : (E143_Finset 4493).card = 4515 := by native_decide
theorem BSD_E143_card_p4507 : (E143_Finset 4507).card = 4534 := by native_decide
theorem BSD_E143_card_p4513 : (E143_Finset 4513).card = 4513 := by native_decide
theorem BSD_E143_card_p4517 : (E143_Finset 4517).card = 4410 := by native_decide
theorem BSD_E143_card_p4519 : (E143_Finset 4519).card = 4497 := by native_decide
theorem BSD_E143_card_p4523 : (E143_Finset 4523).card = 4456 := by native_decide
theorem BSD_E143_card_p4547 : (E143_Finset 4547).card = 4560 := by native_decide
theorem BSD_E143_card_p4549 : (E143_Finset 4549).card = 4474 := by native_decide
theorem BSD_E143_card_p4561 : (E143_Finset 4561).card = 4528 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4483 : a_p 4483 = (-24 : ℤ) := by
  have h := BSD_E143_card_p4483; unfold a_p; omega
theorem BSD_ap_p4493 : a_p 4493 = (-21 : ℤ) := by
  have h := BSD_E143_card_p4493; unfold a_p; omega
theorem BSD_ap_p4507 : a_p 4507 = (-26 : ℤ) := by
  have h := BSD_E143_card_p4507; unfold a_p; omega
theorem BSD_ap_p4513 : a_p 4513 = (1 : ℤ) := by
  have h := BSD_E143_card_p4513; unfold a_p; omega
theorem BSD_ap_p4517 : a_p 4517 = (108 : ℤ) := by
  have h := BSD_E143_card_p4517; unfold a_p; omega
theorem BSD_ap_p4519 : a_p 4519 = (23 : ℤ) := by
  have h := BSD_E143_card_p4519; unfold a_p; omega
theorem BSD_ap_p4523 : a_p 4523 = (68 : ℤ) := by
  have h := BSD_E143_card_p4523; unfold a_p; omega
theorem BSD_ap_p4547 : a_p 4547 = (-12 : ℤ) := by
  have h := BSD_E143_card_p4547; unfold a_p; omega
theorem BSD_ap_p4549 : a_p 4549 = (76 : ℤ) := by
  have h := BSD_E143_card_p4549; unfold a_p; omega
theorem BSD_ap_p4561 : a_p 4561 = (34 : ℤ) := by
  have h := BSD_E143_card_p4561; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4483: a_p=-24, 4p-a_p²=17356
theorem BSD_DegreeNonneg_p4483 : BSD_FrobeniusDegreeNonneg_OPEN 4483 := fun r => by
  have hap : (a_p 4483 : ℝ) = -24 := by exact_mod_cast BSD_ap_p4483
  have key : r ^ 2 - (a_p 4483 : ℝ) * r + ((4483 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 17356/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=4493: a_p=-21, 4p-a_p²=17531
theorem BSD_DegreeNonneg_p4493 : BSD_FrobeniusDegreeNonneg_OPEN 4493 := fun r => by
  have hap : (a_p 4493 : ℝ) = -21 := by exact_mod_cast BSD_ap_p4493
  have key : r ^ 2 - (a_p 4493 : ℝ) * r + ((4493 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 17531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

-- p=4507: a_p=-26, 4p-a_p²=17352
theorem BSD_DegreeNonneg_p4507 : BSD_FrobeniusDegreeNonneg_OPEN 4507 := fun r => by
  have hap : (a_p 4507 : ℝ) = -26 := by exact_mod_cast BSD_ap_p4507
  have key : r ^ 2 - (a_p 4507 : ℝ) * r + ((4507 : ℕ) : ℝ) =
      (r + 26/2) ^ 2 + 17352/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (26 : ℝ)/2)]

-- p=4513: a_p=+1, 4p-a_p²=18051
theorem BSD_DegreeNonneg_p4513 : BSD_FrobeniusDegreeNonneg_OPEN 4513 := fun r => by
  have hap : (a_p 4513 : ℝ) = 1 := by exact_mod_cast BSD_ap_p4513
  have key : r ^ 2 - (a_p 4513 : ℝ) * r + ((4513 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 18051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

-- p=4517: a_p=+108, 4p-a_p²=6404
theorem BSD_DegreeNonneg_p4517 : BSD_FrobeniusDegreeNonneg_OPEN 4517 := fun r => by
  have hap : (a_p 4517 : ℝ) = 108 := by exact_mod_cast BSD_ap_p4517
  have key : r ^ 2 - (a_p 4517 : ℝ) * r + ((4517 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 6404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

-- p=4519: a_p=+23, 4p-a_p²=17547
theorem BSD_DegreeNonneg_p4519 : BSD_FrobeniusDegreeNonneg_OPEN 4519 := fun r => by
  have hap : (a_p 4519 : ℝ) = 23 := by exact_mod_cast BSD_ap_p4519
  have key : r ^ 2 - (a_p 4519 : ℝ) * r + ((4519 : ℕ) : ℝ) =
      (r - 23/2) ^ 2 + 17547/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (23 : ℝ)/2)]

-- p=4523: a_p=+68, 4p-a_p²=13468
theorem BSD_DegreeNonneg_p4523 : BSD_FrobeniusDegreeNonneg_OPEN 4523 := fun r => by
  have hap : (a_p 4523 : ℝ) = 68 := by exact_mod_cast BSD_ap_p4523
  have key : r ^ 2 - (a_p 4523 : ℝ) * r + ((4523 : ℕ) : ℝ) =
      (r - 68/2) ^ 2 + 13468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (68 : ℝ)/2)]

-- p=4547: a_p=-12, 4p-a_p²=18044
theorem BSD_DegreeNonneg_p4547 : BSD_FrobeniusDegreeNonneg_OPEN 4547 := fun r => by
  have hap : (a_p 4547 : ℝ) = -12 := by exact_mod_cast BSD_ap_p4547
  have key : r ^ 2 - (a_p 4547 : ℝ) * r + ((4547 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 18044/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

-- p=4549: a_p=+76, 4p-a_p²=12420
theorem BSD_DegreeNonneg_p4549 : BSD_FrobeniusDegreeNonneg_OPEN 4549 := fun r => by
  have hap : (a_p 4549 : ℝ) = 76 := by exact_mod_cast BSD_ap_p4549
  have key : r ^ 2 - (a_p 4549 : ℝ) * r + ((4549 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 12420/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

-- p=4561: a_p=+34, 4p-a_p²=17088
theorem BSD_DegreeNonneg_p4561 : BSD_FrobeniusDegreeNonneg_OPEN 4561 := fun r => by
  have hap : (a_p 4561 : ℝ) = 34 := by exact_mod_cast BSD_ap_p4561
  have key : r ^ 2 - (a_p 4561 : ℝ) * r + ((4561 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 17088/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4483 : BSD_Hasse_OPEN 4483 :=
  BSD_hasse_of_degree_nonneg 4483 BSD_DegreeNonneg_p4483
theorem BSD_Hasse_OPEN_p4493 : BSD_Hasse_OPEN 4493 :=
  BSD_hasse_of_degree_nonneg 4493 BSD_DegreeNonneg_p4493
theorem BSD_Hasse_OPEN_p4507 : BSD_Hasse_OPEN 4507 :=
  BSD_hasse_of_degree_nonneg 4507 BSD_DegreeNonneg_p4507
theorem BSD_Hasse_OPEN_p4513 : BSD_Hasse_OPEN 4513 :=
  BSD_hasse_of_degree_nonneg 4513 BSD_DegreeNonneg_p4513
theorem BSD_Hasse_OPEN_p4517 : BSD_Hasse_OPEN 4517 :=
  BSD_hasse_of_degree_nonneg 4517 BSD_DegreeNonneg_p4517
theorem BSD_Hasse_OPEN_p4519 : BSD_Hasse_OPEN 4519 :=
  BSD_hasse_of_degree_nonneg 4519 BSD_DegreeNonneg_p4519
theorem BSD_Hasse_OPEN_p4523 : BSD_Hasse_OPEN 4523 :=
  BSD_hasse_of_degree_nonneg 4523 BSD_DegreeNonneg_p4523
theorem BSD_Hasse_OPEN_p4547 : BSD_Hasse_OPEN 4547 :=
  BSD_hasse_of_degree_nonneg 4547 BSD_DegreeNonneg_p4547
theorem BSD_Hasse_OPEN_p4549 : BSD_Hasse_OPEN 4549 :=
  BSD_hasse_of_degree_nonneg 4549 BSD_DegreeNonneg_p4549
theorem BSD_Hasse_OPEN_p4561 : BSD_Hasse_OPEN 4561 :=
  BSD_hasse_of_degree_nonneg 4561 BSD_DegreeNonneg_p4561

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4483 : (a_p 4483 : ℝ) ^ 2 ≤ 4 * (4483 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4483
theorem BSD_HasseBound_Disc_p4493 : (a_p 4493 : ℝ) ^ 2 ≤ 4 * (4493 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4493
theorem BSD_HasseBound_Disc_p4507 : (a_p 4507 : ℝ) ^ 2 ≤ 4 * (4507 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4507
theorem BSD_HasseBound_Disc_p4513 : (a_p 4513 : ℝ) ^ 2 ≤ 4 * (4513 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4513
theorem BSD_HasseBound_Disc_p4517 : (a_p 4517 : ℝ) ^ 2 ≤ 4 * (4517 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4517
theorem BSD_HasseBound_Disc_p4519 : (a_p 4519 : ℝ) ^ 2 ≤ 4 * (4519 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4519
theorem BSD_HasseBound_Disc_p4523 : (a_p 4523 : ℝ) ^ 2 ≤ 4 * (4523 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4523
theorem BSD_HasseBound_Disc_p4547 : (a_p 4547 : ℝ) ^ 2 ≤ 4 * (4547 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4547
theorem BSD_HasseBound_Disc_p4549 : (a_p 4549 : ℝ) ^ 2 ≤ 4 * (4549 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4549
theorem BSD_HasseBound_Disc_p4561 : (a_p 4561 : ℝ) ^ 2 ≤ 4 * (4561 : ℝ) :=
  BSD_disc_from_deg_827 BSD_DegreeNonneg_p4561

end Towers.BSD