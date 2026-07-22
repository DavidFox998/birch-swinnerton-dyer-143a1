/-
================================================================
Towers / BSD / BSD_Genesis788_CLOSED  (genesis-788)

HasseBridge Tier C: Hasse bounds for primes
1367..1439 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1367: card=1328, a_p=+40, disc=-3868
  p=1373: card=1333, a_p=+41, disc=-3811
  p=1381: card=1380, a_p=+2, disc=-5520
  p=1399: card=1390, a_p=+10, disc=-5496
  p=1409: card=1455, a_p=-45, disc=-3611
  p=1423: card=1453, a_p=-29, disc=-4851
  p=1427: card=1458, a_p=-30, disc=-4808
  p=1429: card=1466, a_p=-36, disc=-4420
  p=1433: card=1464, a_p=-30, disc=-4832
  p=1439: card=1500, a_p=-60, disc=-2156

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_788 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i788_p1367 : Fact (1367 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1373 : Fact (1373 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1381 : Fact (1381 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1399 : Fact (1399 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1409 : Fact (1409 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1423 : Fact (1423 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1427 : Fact (1427 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1429 : Fact (1429 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1433 : Fact (1433 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1439 : Fact (1439 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1367 : (E143_Finset 1367).card = 1328 := by native_decide
theorem BSD_E143_card_p1373 : (E143_Finset 1373).card = 1333 := by native_decide
theorem BSD_E143_card_p1381 : (E143_Finset 1381).card = 1380 := by native_decide
theorem BSD_E143_card_p1399 : (E143_Finset 1399).card = 1390 := by native_decide
theorem BSD_E143_card_p1409 : (E143_Finset 1409).card = 1455 := by native_decide
theorem BSD_E143_card_p1423 : (E143_Finset 1423).card = 1453 := by native_decide
theorem BSD_E143_card_p1427 : (E143_Finset 1427).card = 1458 := by native_decide
theorem BSD_E143_card_p1429 : (E143_Finset 1429).card = 1466 := by native_decide
theorem BSD_E143_card_p1433 : (E143_Finset 1433).card = 1464 := by native_decide
theorem BSD_E143_card_p1439 : (E143_Finset 1439).card = 1500 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1367 : a_p 1367 = (40 : ℤ) := by
  have h := BSD_E143_card_p1367; unfold a_p; omega
theorem BSD_ap_p1373 : a_p 1373 = (41 : ℤ) := by
  have h := BSD_E143_card_p1373; unfold a_p; omega
theorem BSD_ap_p1381 : a_p 1381 = (2 : ℤ) := by
  have h := BSD_E143_card_p1381; unfold a_p; omega
theorem BSD_ap_p1399 : a_p 1399 = (10 : ℤ) := by
  have h := BSD_E143_card_p1399; unfold a_p; omega
theorem BSD_ap_p1409 : a_p 1409 = (-45 : ℤ) := by
  have h := BSD_E143_card_p1409; unfold a_p; omega
theorem BSD_ap_p1423 : a_p 1423 = (-29 : ℤ) := by
  have h := BSD_E143_card_p1423; unfold a_p; omega
theorem BSD_ap_p1427 : a_p 1427 = (-30 : ℤ) := by
  have h := BSD_E143_card_p1427; unfold a_p; omega
theorem BSD_ap_p1429 : a_p 1429 = (-36 : ℤ) := by
  have h := BSD_E143_card_p1429; unfold a_p; omega
theorem BSD_ap_p1433 : a_p 1433 = (-30 : ℤ) := by
  have h := BSD_E143_card_p1433; unfold a_p; omega
theorem BSD_ap_p1439 : a_p 1439 = (-60 : ℤ) := by
  have h := BSD_E143_card_p1439; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1367: a_p=+40, 4p-a_p²=3868
theorem BSD_DegreeNonneg_p1367 : BSD_FrobeniusDegreeNonneg_OPEN 1367 := fun r => by
  have hap : (a_p 1367 : ℝ) = 40 := by exact_mod_cast BSD_ap_p1367
  have key : r ^ 2 - (a_p 1367 : ℝ) * r + ((1367 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 3868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

-- p=1373: a_p=+41, 4p-a_p²=3811
theorem BSD_DegreeNonneg_p1373 : BSD_FrobeniusDegreeNonneg_OPEN 1373 := fun r => by
  have hap : (a_p 1373 : ℝ) = 41 := by exact_mod_cast BSD_ap_p1373
  have key : r ^ 2 - (a_p 1373 : ℝ) * r + ((1373 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 3811/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

-- p=1381: a_p=+2, 4p-a_p²=5520
theorem BSD_DegreeNonneg_p1381 : BSD_FrobeniusDegreeNonneg_OPEN 1381 := fun r => by
  have hap : (a_p 1381 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1381
  have key : r ^ 2 - (a_p 1381 : ℝ) * r + ((1381 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 5520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

-- p=1399: a_p=+10, 4p-a_p²=5496
theorem BSD_DegreeNonneg_p1399 : BSD_FrobeniusDegreeNonneg_OPEN 1399 := fun r => by
  have hap : (a_p 1399 : ℝ) = 10 := by exact_mod_cast BSD_ap_p1399
  have key : r ^ 2 - (a_p 1399 : ℝ) * r + ((1399 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 5496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

-- p=1409: a_p=-45, 4p-a_p²=3611
theorem BSD_DegreeNonneg_p1409 : BSD_FrobeniusDegreeNonneg_OPEN 1409 := fun r => by
  have hap : (a_p 1409 : ℝ) = -45 := by exact_mod_cast BSD_ap_p1409
  have key : r ^ 2 - (a_p 1409 : ℝ) * r + ((1409 : ℕ) : ℝ) =
      (r + 45/2) ^ 2 + 3611/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (45 : ℝ)/2)]

-- p=1423: a_p=-29, 4p-a_p²=4851
theorem BSD_DegreeNonneg_p1423 : BSD_FrobeniusDegreeNonneg_OPEN 1423 := fun r => by
  have hap : (a_p 1423 : ℝ) = -29 := by exact_mod_cast BSD_ap_p1423
  have key : r ^ 2 - (a_p 1423 : ℝ) * r + ((1423 : ℕ) : ℝ) =
      (r + 29/2) ^ 2 + 4851/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (29 : ℝ)/2)]

-- p=1427: a_p=-30, 4p-a_p²=4808
theorem BSD_DegreeNonneg_p1427 : BSD_FrobeniusDegreeNonneg_OPEN 1427 := fun r => by
  have hap : (a_p 1427 : ℝ) = -30 := by exact_mod_cast BSD_ap_p1427
  have key : r ^ 2 - (a_p 1427 : ℝ) * r + ((1427 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 4808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

-- p=1429: a_p=-36, 4p-a_p²=4420
theorem BSD_DegreeNonneg_p1429 : BSD_FrobeniusDegreeNonneg_OPEN 1429 := fun r => by
  have hap : (a_p 1429 : ℝ) = -36 := by exact_mod_cast BSD_ap_p1429
  have key : r ^ 2 - (a_p 1429 : ℝ) * r + ((1429 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 4420/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

-- p=1433: a_p=-30, 4p-a_p²=4832
theorem BSD_DegreeNonneg_p1433 : BSD_FrobeniusDegreeNonneg_OPEN 1433 := fun r => by
  have hap : (a_p 1433 : ℝ) = -30 := by exact_mod_cast BSD_ap_p1433
  have key : r ^ 2 - (a_p 1433 : ℝ) * r + ((1433 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 4832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

-- p=1439: a_p=-60, 4p-a_p²=2156
theorem BSD_DegreeNonneg_p1439 : BSD_FrobeniusDegreeNonneg_OPEN 1439 := fun r => by
  have hap : (a_p 1439 : ℝ) = -60 := by exact_mod_cast BSD_ap_p1439
  have key : r ^ 2 - (a_p 1439 : ℝ) * r + ((1439 : ℕ) : ℝ) =
      (r + 60/2) ^ 2 + 2156/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (60 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1367 : BSD_Hasse_OPEN 1367 :=
  BSD_hasse_of_degree_nonneg 1367 BSD_DegreeNonneg_p1367
theorem BSD_Hasse_OPEN_p1373 : BSD_Hasse_OPEN 1373 :=
  BSD_hasse_of_degree_nonneg 1373 BSD_DegreeNonneg_p1373
theorem BSD_Hasse_OPEN_p1381 : BSD_Hasse_OPEN 1381 :=
  BSD_hasse_of_degree_nonneg 1381 BSD_DegreeNonneg_p1381
theorem BSD_Hasse_OPEN_p1399 : BSD_Hasse_OPEN 1399 :=
  BSD_hasse_of_degree_nonneg 1399 BSD_DegreeNonneg_p1399
theorem BSD_Hasse_OPEN_p1409 : BSD_Hasse_OPEN 1409 :=
  BSD_hasse_of_degree_nonneg 1409 BSD_DegreeNonneg_p1409
theorem BSD_Hasse_OPEN_p1423 : BSD_Hasse_OPEN 1423 :=
  BSD_hasse_of_degree_nonneg 1423 BSD_DegreeNonneg_p1423
theorem BSD_Hasse_OPEN_p1427 : BSD_Hasse_OPEN 1427 :=
  BSD_hasse_of_degree_nonneg 1427 BSD_DegreeNonneg_p1427
theorem BSD_Hasse_OPEN_p1429 : BSD_Hasse_OPEN 1429 :=
  BSD_hasse_of_degree_nonneg 1429 BSD_DegreeNonneg_p1429
theorem BSD_Hasse_OPEN_p1433 : BSD_Hasse_OPEN 1433 :=
  BSD_hasse_of_degree_nonneg 1433 BSD_DegreeNonneg_p1433
theorem BSD_Hasse_OPEN_p1439 : BSD_Hasse_OPEN 1439 :=
  BSD_hasse_of_degree_nonneg 1439 BSD_DegreeNonneg_p1439

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1367 : (a_p 1367 : ℝ) ^ 2 ≤ 4 * (1367 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1367
theorem BSD_HasseBound_Disc_p1373 : (a_p 1373 : ℝ) ^ 2 ≤ 4 * (1373 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1373
theorem BSD_HasseBound_Disc_p1381 : (a_p 1381 : ℝ) ^ 2 ≤ 4 * (1381 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1381
theorem BSD_HasseBound_Disc_p1399 : (a_p 1399 : ℝ) ^ 2 ≤ 4 * (1399 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1399
theorem BSD_HasseBound_Disc_p1409 : (a_p 1409 : ℝ) ^ 2 ≤ 4 * (1409 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1409
theorem BSD_HasseBound_Disc_p1423 : (a_p 1423 : ℝ) ^ 2 ≤ 4 * (1423 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1423
theorem BSD_HasseBound_Disc_p1427 : (a_p 1427 : ℝ) ^ 2 ≤ 4 * (1427 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1427
theorem BSD_HasseBound_Disc_p1429 : (a_p 1429 : ℝ) ^ 2 ≤ 4 * (1429 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1429
theorem BSD_HasseBound_Disc_p1433 : (a_p 1433 : ℝ) ^ 2 ≤ 4 * (1433 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1433
theorem BSD_HasseBound_Disc_p1439 : (a_p 1439 : ℝ) ^ 2 ≤ 4 * (1439 : ℝ) :=
  BSD_disc_from_deg_788 BSD_DegreeNonneg_p1439

end Towers.BSD