/-
================================================================
Towers / BSD / BSD_Genesis883_CLOSED  (genesis-883)

HasseBridge Tier C: Hasse bounds for primes
9437..9511 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9437: card=9490, a_p=-52, disc=-35044
  p=9439: card=9407, a_p=+33, disc=-36667
  p=9461: card=9292, a_p=+170, disc=-8944
  p=9463: card=9280, a_p=+184, disc=-3996
  p=9467: card=9556, a_p=-88, disc=-30124
  p=9473: card=9518, a_p=-44, disc=-35956
  p=9479: card=9458, a_p=+22, disc=-37432
  p=9491: card=9552, a_p=-60, disc=-34364
  p=9497: card=9383, a_p=+115, disc=-24763
  p=9511: card=9396, a_p=+116, disc=-24588

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_883 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i883_p9437 : Fact (9437 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9439 : Fact (9439 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9461 : Fact (9461 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9463 : Fact (9463 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9467 : Fact (9467 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9473 : Fact (9473 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9479 : Fact (9479 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9491 : Fact (9491 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9497 : Fact (9497 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9511 : Fact (9511 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9437 : (E143_Finset 9437).card = 9490 := by native_decide
theorem BSD_E143_card_p9439 : (E143_Finset 9439).card = 9407 := by native_decide
theorem BSD_E143_card_p9461 : (E143_Finset 9461).card = 9292 := by native_decide
theorem BSD_E143_card_p9463 : (E143_Finset 9463).card = 9280 := by native_decide
theorem BSD_E143_card_p9467 : (E143_Finset 9467).card = 9556 := by native_decide
theorem BSD_E143_card_p9473 : (E143_Finset 9473).card = 9518 := by native_decide
theorem BSD_E143_card_p9479 : (E143_Finset 9479).card = 9458 := by native_decide
theorem BSD_E143_card_p9491 : (E143_Finset 9491).card = 9552 := by native_decide
theorem BSD_E143_card_p9497 : (E143_Finset 9497).card = 9383 := by native_decide
theorem BSD_E143_card_p9511 : (E143_Finset 9511).card = 9396 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9437 : a_p 9437 = (-52 : ℤ) := by
  have h := BSD_E143_card_p9437; unfold a_p; omega
theorem BSD_ap_p9439 : a_p 9439 = (33 : ℤ) := by
  have h := BSD_E143_card_p9439; unfold a_p; omega
theorem BSD_ap_p9461 : a_p 9461 = (170 : ℤ) := by
  have h := BSD_E143_card_p9461; unfold a_p; omega
theorem BSD_ap_p9463 : a_p 9463 = (184 : ℤ) := by
  have h := BSD_E143_card_p9463; unfold a_p; omega
theorem BSD_ap_p9467 : a_p 9467 = (-88 : ℤ) := by
  have h := BSD_E143_card_p9467; unfold a_p; omega
theorem BSD_ap_p9473 : a_p 9473 = (-44 : ℤ) := by
  have h := BSD_E143_card_p9473; unfold a_p; omega
theorem BSD_ap_p9479 : a_p 9479 = (22 : ℤ) := by
  have h := BSD_E143_card_p9479; unfold a_p; omega
theorem BSD_ap_p9491 : a_p 9491 = (-60 : ℤ) := by
  have h := BSD_E143_card_p9491; unfold a_p; omega
theorem BSD_ap_p9497 : a_p 9497 = (115 : ℤ) := by
  have h := BSD_E143_card_p9497; unfold a_p; omega
theorem BSD_ap_p9511 : a_p 9511 = (116 : ℤ) := by
  have h := BSD_E143_card_p9511; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9437: a_p=-52, 4p-a_p²=35044
theorem BSD_DegreeNonneg_p9437 : BSD_FrobeniusDegreeNonneg_OPEN 9437 := fun r => by
  have hap : (a_p 9437 : ℝ) = -52 := by exact_mod_cast BSD_ap_p9437
  have key : r ^ 2 - (a_p 9437 : ℝ) * r + ((9437 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 35044/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

-- p=9439: a_p=+33, 4p-a_p²=36667
theorem BSD_DegreeNonneg_p9439 : BSD_FrobeniusDegreeNonneg_OPEN 9439 := fun r => by
  have hap : (a_p 9439 : ℝ) = 33 := by exact_mod_cast BSD_ap_p9439
  have key : r ^ 2 - (a_p 9439 : ℝ) * r + ((9439 : ℕ) : ℝ) =
      (r - 33/2) ^ 2 + 36667/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (33 : ℝ)/2)]

-- p=9461: a_p=+170, 4p-a_p²=8944
theorem BSD_DegreeNonneg_p9461 : BSD_FrobeniusDegreeNonneg_OPEN 9461 := fun r => by
  have hap : (a_p 9461 : ℝ) = 170 := by exact_mod_cast BSD_ap_p9461
  have key : r ^ 2 - (a_p 9461 : ℝ) * r + ((9461 : ℕ) : ℝ) =
      (r - 170/2) ^ 2 + 8944/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (170 : ℝ)/2)]

-- p=9463: a_p=+184, 4p-a_p²=3996
theorem BSD_DegreeNonneg_p9463 : BSD_FrobeniusDegreeNonneg_OPEN 9463 := fun r => by
  have hap : (a_p 9463 : ℝ) = 184 := by exact_mod_cast BSD_ap_p9463
  have key : r ^ 2 - (a_p 9463 : ℝ) * r + ((9463 : ℕ) : ℝ) =
      (r - 184/2) ^ 2 + 3996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (184 : ℝ)/2)]

-- p=9467: a_p=-88, 4p-a_p²=30124
theorem BSD_DegreeNonneg_p9467 : BSD_FrobeniusDegreeNonneg_OPEN 9467 := fun r => by
  have hap : (a_p 9467 : ℝ) = -88 := by exact_mod_cast BSD_ap_p9467
  have key : r ^ 2 - (a_p 9467 : ℝ) * r + ((9467 : ℕ) : ℝ) =
      (r + 88/2) ^ 2 + 30124/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (88 : ℝ)/2)]

-- p=9473: a_p=-44, 4p-a_p²=35956
theorem BSD_DegreeNonneg_p9473 : BSD_FrobeniusDegreeNonneg_OPEN 9473 := fun r => by
  have hap : (a_p 9473 : ℝ) = -44 := by exact_mod_cast BSD_ap_p9473
  have key : r ^ 2 - (a_p 9473 : ℝ) * r + ((9473 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 35956/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

-- p=9479: a_p=+22, 4p-a_p²=37432
theorem BSD_DegreeNonneg_p9479 : BSD_FrobeniusDegreeNonneg_OPEN 9479 := fun r => by
  have hap : (a_p 9479 : ℝ) = 22 := by exact_mod_cast BSD_ap_p9479
  have key : r ^ 2 - (a_p 9479 : ℝ) * r + ((9479 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 37432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

-- p=9491: a_p=-60, 4p-a_p²=34364
theorem BSD_DegreeNonneg_p9491 : BSD_FrobeniusDegreeNonneg_OPEN 9491 := fun r => by
  have hap : (a_p 9491 : ℝ) = -60 := by exact_mod_cast BSD_ap_p9491
  have key : r ^ 2 - (a_p 9491 : ℝ) * r + ((9491 : ℕ) : ℝ) =
      (r + 60/2) ^ 2 + 34364/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (60 : ℝ)/2)]

-- p=9497: a_p=+115, 4p-a_p²=24763
theorem BSD_DegreeNonneg_p9497 : BSD_FrobeniusDegreeNonneg_OPEN 9497 := fun r => by
  have hap : (a_p 9497 : ℝ) = 115 := by exact_mod_cast BSD_ap_p9497
  have key : r ^ 2 - (a_p 9497 : ℝ) * r + ((9497 : ℕ) : ℝ) =
      (r - 115/2) ^ 2 + 24763/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (115 : ℝ)/2)]

-- p=9511: a_p=+116, 4p-a_p²=24588
theorem BSD_DegreeNonneg_p9511 : BSD_FrobeniusDegreeNonneg_OPEN 9511 := fun r => by
  have hap : (a_p 9511 : ℝ) = 116 := by exact_mod_cast BSD_ap_p9511
  have key : r ^ 2 - (a_p 9511 : ℝ) * r + ((9511 : ℕ) : ℝ) =
      (r - 116/2) ^ 2 + 24588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (116 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9437 : BSD_Hasse_OPEN 9437 :=
  BSD_hasse_of_degree_nonneg 9437 BSD_DegreeNonneg_p9437
theorem BSD_Hasse_OPEN_p9439 : BSD_Hasse_OPEN 9439 :=
  BSD_hasse_of_degree_nonneg 9439 BSD_DegreeNonneg_p9439
theorem BSD_Hasse_OPEN_p9461 : BSD_Hasse_OPEN 9461 :=
  BSD_hasse_of_degree_nonneg 9461 BSD_DegreeNonneg_p9461
theorem BSD_Hasse_OPEN_p9463 : BSD_Hasse_OPEN 9463 :=
  BSD_hasse_of_degree_nonneg 9463 BSD_DegreeNonneg_p9463
theorem BSD_Hasse_OPEN_p9467 : BSD_Hasse_OPEN 9467 :=
  BSD_hasse_of_degree_nonneg 9467 BSD_DegreeNonneg_p9467
theorem BSD_Hasse_OPEN_p9473 : BSD_Hasse_OPEN 9473 :=
  BSD_hasse_of_degree_nonneg 9473 BSD_DegreeNonneg_p9473
theorem BSD_Hasse_OPEN_p9479 : BSD_Hasse_OPEN 9479 :=
  BSD_hasse_of_degree_nonneg 9479 BSD_DegreeNonneg_p9479
theorem BSD_Hasse_OPEN_p9491 : BSD_Hasse_OPEN 9491 :=
  BSD_hasse_of_degree_nonneg 9491 BSD_DegreeNonneg_p9491
theorem BSD_Hasse_OPEN_p9497 : BSD_Hasse_OPEN 9497 :=
  BSD_hasse_of_degree_nonneg 9497 BSD_DegreeNonneg_p9497
theorem BSD_Hasse_OPEN_p9511 : BSD_Hasse_OPEN 9511 :=
  BSD_hasse_of_degree_nonneg 9511 BSD_DegreeNonneg_p9511

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9437 : (a_p 9437 : ℝ) ^ 2 ≤ 4 * (9437 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9437
theorem BSD_HasseBound_Disc_p9439 : (a_p 9439 : ℝ) ^ 2 ≤ 4 * (9439 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9439
theorem BSD_HasseBound_Disc_p9461 : (a_p 9461 : ℝ) ^ 2 ≤ 4 * (9461 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9461
theorem BSD_HasseBound_Disc_p9463 : (a_p 9463 : ℝ) ^ 2 ≤ 4 * (9463 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9463
theorem BSD_HasseBound_Disc_p9467 : (a_p 9467 : ℝ) ^ 2 ≤ 4 * (9467 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9467
theorem BSD_HasseBound_Disc_p9473 : (a_p 9473 : ℝ) ^ 2 ≤ 4 * (9473 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9473
theorem BSD_HasseBound_Disc_p9479 : (a_p 9479 : ℝ) ^ 2 ≤ 4 * (9479 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9479
theorem BSD_HasseBound_Disc_p9491 : (a_p 9491 : ℝ) ^ 2 ≤ 4 * (9491 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9491
theorem BSD_HasseBound_Disc_p9497 : (a_p 9497 : ℝ) ^ 2 ≤ 4 * (9497 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9497
theorem BSD_HasseBound_Disc_p9511 : (a_p 9511 : ℝ) ^ 2 ≤ 4 * (9511 : ℝ) :=
  BSD_disc_from_deg_883 BSD_DegreeNonneg_p9511

end Towers.BSD