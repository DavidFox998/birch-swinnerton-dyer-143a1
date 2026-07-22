/-
================================================================
Towers / BSD / BSD_Genesis789_CLOSED  (genesis-789)

HasseBridge Tier C: Hasse bounds for primes
1447..1493 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1447: card=1476, a_p=-28, disc=-5004
  p=1451: card=1452, a_p=+0, disc=-5804
  p=1453: card=1485, a_p=-31, disc=-4851
  p=1459: card=1460, a_p=+0, disc=-5836
  p=1471: card=1524, a_p=-52, disc=-3180
  p=1481: card=1436, a_p=+46, disc=-3808
  p=1483: card=1503, a_p=-19, disc=-5571
  p=1487: card=1428, a_p=+60, disc=-2348
  p=1489: card=1499, a_p=-9, disc=-5875
  p=1493: card=1538, a_p=-44, disc=-4036

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_789 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i789_p1447 : Fact (1447 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1451 : Fact (1451 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1453 : Fact (1453 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1459 : Fact (1459 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1471 : Fact (1471 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1481 : Fact (1481 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1483 : Fact (1483 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1487 : Fact (1487 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1489 : Fact (1489 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1493 : Fact (1493 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1447 : (E143_Finset 1447).card = 1476 := by native_decide
theorem BSD_E143_card_p1451 : (E143_Finset 1451).card = 1452 := by native_decide
theorem BSD_E143_card_p1453 : (E143_Finset 1453).card = 1485 := by native_decide
theorem BSD_E143_card_p1459 : (E143_Finset 1459).card = 1460 := by native_decide
theorem BSD_E143_card_p1471 : (E143_Finset 1471).card = 1524 := by native_decide
theorem BSD_E143_card_p1481 : (E143_Finset 1481).card = 1436 := by native_decide
theorem BSD_E143_card_p1483 : (E143_Finset 1483).card = 1503 := by native_decide
theorem BSD_E143_card_p1487 : (E143_Finset 1487).card = 1428 := by native_decide
theorem BSD_E143_card_p1489 : (E143_Finset 1489).card = 1499 := by native_decide
theorem BSD_E143_card_p1493 : (E143_Finset 1493).card = 1538 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1447 : a_p 1447 = (-28 : ℤ) := by
  have h := BSD_E143_card_p1447; unfold a_p; omega
theorem BSD_ap_p1451 : a_p 1451 = (0 : ℤ) := by
  have h := BSD_E143_card_p1451; unfold a_p; omega
theorem BSD_ap_p1453 : a_p 1453 = (-31 : ℤ) := by
  have h := BSD_E143_card_p1453; unfold a_p; omega
theorem BSD_ap_p1459 : a_p 1459 = (0 : ℤ) := by
  have h := BSD_E143_card_p1459; unfold a_p; omega
theorem BSD_ap_p1471 : a_p 1471 = (-52 : ℤ) := by
  have h := BSD_E143_card_p1471; unfold a_p; omega
theorem BSD_ap_p1481 : a_p 1481 = (46 : ℤ) := by
  have h := BSD_E143_card_p1481; unfold a_p; omega
theorem BSD_ap_p1483 : a_p 1483 = (-19 : ℤ) := by
  have h := BSD_E143_card_p1483; unfold a_p; omega
theorem BSD_ap_p1487 : a_p 1487 = (60 : ℤ) := by
  have h := BSD_E143_card_p1487; unfold a_p; omega
theorem BSD_ap_p1489 : a_p 1489 = (-9 : ℤ) := by
  have h := BSD_E143_card_p1489; unfold a_p; omega
theorem BSD_ap_p1493 : a_p 1493 = (-44 : ℤ) := by
  have h := BSD_E143_card_p1493; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1447: a_p=-28, 4p-a_p²=5004
theorem BSD_DegreeNonneg_p1447 : BSD_FrobeniusDegreeNonneg_OPEN 1447 := fun r => by
  have hap : (a_p 1447 : ℝ) = -28 := by exact_mod_cast BSD_ap_p1447
  have key : r ^ 2 - (a_p 1447 : ℝ) * r + ((1447 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 5004/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

-- p=1451: a_p=+0, 4p-a_p²=5804
theorem BSD_DegreeNonneg_p1451 : BSD_FrobeniusDegreeNonneg_OPEN 1451 := fun r => by
  have hap : (a_p 1451 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1451
  have key : r ^ 2 - (a_p 1451 : ℝ) * r + ((1451 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 5804/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=1453: a_p=-31, 4p-a_p²=4851
theorem BSD_DegreeNonneg_p1453 : BSD_FrobeniusDegreeNonneg_OPEN 1453 := fun r => by
  have hap : (a_p 1453 : ℝ) = -31 := by exact_mod_cast BSD_ap_p1453
  have key : r ^ 2 - (a_p 1453 : ℝ) * r + ((1453 : ℕ) : ℝ) =
      (r + 31/2) ^ 2 + 4851/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (31 : ℝ)/2)]

-- p=1459: a_p=+0, 4p-a_p²=5836
theorem BSD_DegreeNonneg_p1459 : BSD_FrobeniusDegreeNonneg_OPEN 1459 := fun r => by
  have hap : (a_p 1459 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1459
  have key : r ^ 2 - (a_p 1459 : ℝ) * r + ((1459 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 5836/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=1471: a_p=-52, 4p-a_p²=3180
theorem BSD_DegreeNonneg_p1471 : BSD_FrobeniusDegreeNonneg_OPEN 1471 := fun r => by
  have hap : (a_p 1471 : ℝ) = -52 := by exact_mod_cast BSD_ap_p1471
  have key : r ^ 2 - (a_p 1471 : ℝ) * r + ((1471 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 3180/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

-- p=1481: a_p=+46, 4p-a_p²=3808
theorem BSD_DegreeNonneg_p1481 : BSD_FrobeniusDegreeNonneg_OPEN 1481 := fun r => by
  have hap : (a_p 1481 : ℝ) = 46 := by exact_mod_cast BSD_ap_p1481
  have key : r ^ 2 - (a_p 1481 : ℝ) * r + ((1481 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 3808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=1483: a_p=-19, 4p-a_p²=5571
theorem BSD_DegreeNonneg_p1483 : BSD_FrobeniusDegreeNonneg_OPEN 1483 := fun r => by
  have hap : (a_p 1483 : ℝ) = -19 := by exact_mod_cast BSD_ap_p1483
  have key : r ^ 2 - (a_p 1483 : ℝ) * r + ((1483 : ℕ) : ℝ) =
      (r + 19/2) ^ 2 + 5571/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (19 : ℝ)/2)]

-- p=1487: a_p=+60, 4p-a_p²=2348
theorem BSD_DegreeNonneg_p1487 : BSD_FrobeniusDegreeNonneg_OPEN 1487 := fun r => by
  have hap : (a_p 1487 : ℝ) = 60 := by exact_mod_cast BSD_ap_p1487
  have key : r ^ 2 - (a_p 1487 : ℝ) * r + ((1487 : ℕ) : ℝ) =
      (r - 60/2) ^ 2 + 2348/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (60 : ℝ)/2)]

-- p=1489: a_p=-9, 4p-a_p²=5875
theorem BSD_DegreeNonneg_p1489 : BSD_FrobeniusDegreeNonneg_OPEN 1489 := fun r => by
  have hap : (a_p 1489 : ℝ) = -9 := by exact_mod_cast BSD_ap_p1489
  have key : r ^ 2 - (a_p 1489 : ℝ) * r + ((1489 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 5875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

-- p=1493: a_p=-44, 4p-a_p²=4036
theorem BSD_DegreeNonneg_p1493 : BSD_FrobeniusDegreeNonneg_OPEN 1493 := fun r => by
  have hap : (a_p 1493 : ℝ) = -44 := by exact_mod_cast BSD_ap_p1493
  have key : r ^ 2 - (a_p 1493 : ℝ) * r + ((1493 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 4036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1447 : BSD_Hasse_OPEN 1447 :=
  BSD_hasse_of_degree_nonneg 1447 BSD_DegreeNonneg_p1447
theorem BSD_Hasse_OPEN_p1451 : BSD_Hasse_OPEN 1451 :=
  BSD_hasse_of_degree_nonneg 1451 BSD_DegreeNonneg_p1451
theorem BSD_Hasse_OPEN_p1453 : BSD_Hasse_OPEN 1453 :=
  BSD_hasse_of_degree_nonneg 1453 BSD_DegreeNonneg_p1453
theorem BSD_Hasse_OPEN_p1459 : BSD_Hasse_OPEN 1459 :=
  BSD_hasse_of_degree_nonneg 1459 BSD_DegreeNonneg_p1459
theorem BSD_Hasse_OPEN_p1471 : BSD_Hasse_OPEN 1471 :=
  BSD_hasse_of_degree_nonneg 1471 BSD_DegreeNonneg_p1471
theorem BSD_Hasse_OPEN_p1481 : BSD_Hasse_OPEN 1481 :=
  BSD_hasse_of_degree_nonneg 1481 BSD_DegreeNonneg_p1481
theorem BSD_Hasse_OPEN_p1483 : BSD_Hasse_OPEN 1483 :=
  BSD_hasse_of_degree_nonneg 1483 BSD_DegreeNonneg_p1483
theorem BSD_Hasse_OPEN_p1487 : BSD_Hasse_OPEN 1487 :=
  BSD_hasse_of_degree_nonneg 1487 BSD_DegreeNonneg_p1487
theorem BSD_Hasse_OPEN_p1489 : BSD_Hasse_OPEN 1489 :=
  BSD_hasse_of_degree_nonneg 1489 BSD_DegreeNonneg_p1489
theorem BSD_Hasse_OPEN_p1493 : BSD_Hasse_OPEN 1493 :=
  BSD_hasse_of_degree_nonneg 1493 BSD_DegreeNonneg_p1493

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1447 : (a_p 1447 : ℝ) ^ 2 ≤ 4 * (1447 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1447
theorem BSD_HasseBound_Disc_p1451 : (a_p 1451 : ℝ) ^ 2 ≤ 4 * (1451 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1451
theorem BSD_HasseBound_Disc_p1453 : (a_p 1453 : ℝ) ^ 2 ≤ 4 * (1453 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1453
theorem BSD_HasseBound_Disc_p1459 : (a_p 1459 : ℝ) ^ 2 ≤ 4 * (1459 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1459
theorem BSD_HasseBound_Disc_p1471 : (a_p 1471 : ℝ) ^ 2 ≤ 4 * (1471 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1471
theorem BSD_HasseBound_Disc_p1481 : (a_p 1481 : ℝ) ^ 2 ≤ 4 * (1481 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1481
theorem BSD_HasseBound_Disc_p1483 : (a_p 1483 : ℝ) ^ 2 ≤ 4 * (1483 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1483
theorem BSD_HasseBound_Disc_p1487 : (a_p 1487 : ℝ) ^ 2 ≤ 4 * (1487 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1487
theorem BSD_HasseBound_Disc_p1489 : (a_p 1489 : ℝ) ^ 2 ≤ 4 * (1489 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1489
theorem BSD_HasseBound_Disc_p1493 : (a_p 1493 : ℝ) ^ 2 ≤ 4 * (1493 : ℝ) :=
  BSD_disc_from_deg_789 BSD_DegreeNonneg_p1493

end Towers.BSD