/-
================================================================
Towers / BSD / BSD_Genesis849_CLOSED  (genesis-849)

HasseBridge Tier C: Hasse bounds for primes
6361..6451 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6361: card=6468, a_p=-106, disc=-14208
  p=6367: card=6400, a_p=-32, disc=-24444
  p=6373: card=6456, a_p=-82, disc=-18768
  p=6379: card=6434, a_p=-54, disc=-22600
  p=6389: card=6291, a_p=+99, disc=-15755
  p=6397: card=6490, a_p=-92, disc=-17124
  p=6421: card=6390, a_p=+32, disc=-24660
  p=6427: card=6399, a_p=+29, disc=-24867
  p=6449: card=6425, a_p=+25, disc=-25171
  p=6451: card=6464, a_p=-12, disc=-25660

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_849 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i849_p6361 : Fact (6361 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6367 : Fact (6367 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6373 : Fact (6373 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6379 : Fact (6379 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6389 : Fact (6389 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6397 : Fact (6397 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6421 : Fact (6421 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6427 : Fact (6427 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6449 : Fact (6449 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6451 : Fact (6451 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6361 : (E143_Finset 6361).card = 6468 := by native_decide
theorem BSD_E143_card_p6367 : (E143_Finset 6367).card = 6400 := by native_decide
theorem BSD_E143_card_p6373 : (E143_Finset 6373).card = 6456 := by native_decide
theorem BSD_E143_card_p6379 : (E143_Finset 6379).card = 6434 := by native_decide
theorem BSD_E143_card_p6389 : (E143_Finset 6389).card = 6291 := by native_decide
theorem BSD_E143_card_p6397 : (E143_Finset 6397).card = 6490 := by native_decide
theorem BSD_E143_card_p6421 : (E143_Finset 6421).card = 6390 := by native_decide
theorem BSD_E143_card_p6427 : (E143_Finset 6427).card = 6399 := by native_decide
theorem BSD_E143_card_p6449 : (E143_Finset 6449).card = 6425 := by native_decide
theorem BSD_E143_card_p6451 : (E143_Finset 6451).card = 6464 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6361 : a_p 6361 = (-106 : ℤ) := by
  have h := BSD_E143_card_p6361; unfold a_p; omega
theorem BSD_ap_p6367 : a_p 6367 = (-32 : ℤ) := by
  have h := BSD_E143_card_p6367; unfold a_p; omega
theorem BSD_ap_p6373 : a_p 6373 = (-82 : ℤ) := by
  have h := BSD_E143_card_p6373; unfold a_p; omega
theorem BSD_ap_p6379 : a_p 6379 = (-54 : ℤ) := by
  have h := BSD_E143_card_p6379; unfold a_p; omega
theorem BSD_ap_p6389 : a_p 6389 = (99 : ℤ) := by
  have h := BSD_E143_card_p6389; unfold a_p; omega
theorem BSD_ap_p6397 : a_p 6397 = (-92 : ℤ) := by
  have h := BSD_E143_card_p6397; unfold a_p; omega
theorem BSD_ap_p6421 : a_p 6421 = (32 : ℤ) := by
  have h := BSD_E143_card_p6421; unfold a_p; omega
theorem BSD_ap_p6427 : a_p 6427 = (29 : ℤ) := by
  have h := BSD_E143_card_p6427; unfold a_p; omega
theorem BSD_ap_p6449 : a_p 6449 = (25 : ℤ) := by
  have h := BSD_E143_card_p6449; unfold a_p; omega
theorem BSD_ap_p6451 : a_p 6451 = (-12 : ℤ) := by
  have h := BSD_E143_card_p6451; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6361: a_p=-106, 4p-a_p²=14208
theorem BSD_DegreeNonneg_p6361 : BSD_FrobeniusDegreeNonneg_OPEN 6361 := fun r => by
  have hap : (a_p 6361 : ℝ) = -106 := by exact_mod_cast BSD_ap_p6361
  have key : r ^ 2 - (a_p 6361 : ℝ) * r + ((6361 : ℕ) : ℝ) =
      (r + 106/2) ^ 2 + 14208/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (106 : ℝ)/2)]

-- p=6367: a_p=-32, 4p-a_p²=24444
theorem BSD_DegreeNonneg_p6367 : BSD_FrobeniusDegreeNonneg_OPEN 6367 := fun r => by
  have hap : (a_p 6367 : ℝ) = -32 := by exact_mod_cast BSD_ap_p6367
  have key : r ^ 2 - (a_p 6367 : ℝ) * r + ((6367 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 24444/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=6373: a_p=-82, 4p-a_p²=18768
theorem BSD_DegreeNonneg_p6373 : BSD_FrobeniusDegreeNonneg_OPEN 6373 := fun r => by
  have hap : (a_p 6373 : ℝ) = -82 := by exact_mod_cast BSD_ap_p6373
  have key : r ^ 2 - (a_p 6373 : ℝ) * r + ((6373 : ℕ) : ℝ) =
      (r + 82/2) ^ 2 + 18768/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (82 : ℝ)/2)]

-- p=6379: a_p=-54, 4p-a_p²=22600
theorem BSD_DegreeNonneg_p6379 : BSD_FrobeniusDegreeNonneg_OPEN 6379 := fun r => by
  have hap : (a_p 6379 : ℝ) = -54 := by exact_mod_cast BSD_ap_p6379
  have key : r ^ 2 - (a_p 6379 : ℝ) * r + ((6379 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 22600/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

-- p=6389: a_p=+99, 4p-a_p²=15755
theorem BSD_DegreeNonneg_p6389 : BSD_FrobeniusDegreeNonneg_OPEN 6389 := fun r => by
  have hap : (a_p 6389 : ℝ) = 99 := by exact_mod_cast BSD_ap_p6389
  have key : r ^ 2 - (a_p 6389 : ℝ) * r + ((6389 : ℕ) : ℝ) =
      (r - 99/2) ^ 2 + 15755/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (99 : ℝ)/2)]

-- p=6397: a_p=-92, 4p-a_p²=17124
theorem BSD_DegreeNonneg_p6397 : BSD_FrobeniusDegreeNonneg_OPEN 6397 := fun r => by
  have hap : (a_p 6397 : ℝ) = -92 := by exact_mod_cast BSD_ap_p6397
  have key : r ^ 2 - (a_p 6397 : ℝ) * r + ((6397 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 17124/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

-- p=6421: a_p=+32, 4p-a_p²=24660
theorem BSD_DegreeNonneg_p6421 : BSD_FrobeniusDegreeNonneg_OPEN 6421 := fun r => by
  have hap : (a_p 6421 : ℝ) = 32 := by exact_mod_cast BSD_ap_p6421
  have key : r ^ 2 - (a_p 6421 : ℝ) * r + ((6421 : ℕ) : ℝ) =
      (r - 32/2) ^ 2 + 24660/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (32 : ℝ)/2)]

-- p=6427: a_p=+29, 4p-a_p²=24867
theorem BSD_DegreeNonneg_p6427 : BSD_FrobeniusDegreeNonneg_OPEN 6427 := fun r => by
  have hap : (a_p 6427 : ℝ) = 29 := by exact_mod_cast BSD_ap_p6427
  have key : r ^ 2 - (a_p 6427 : ℝ) * r + ((6427 : ℕ) : ℝ) =
      (r - 29/2) ^ 2 + 24867/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (29 : ℝ)/2)]

-- p=6449: a_p=+25, 4p-a_p²=25171
theorem BSD_DegreeNonneg_p6449 : BSD_FrobeniusDegreeNonneg_OPEN 6449 := fun r => by
  have hap : (a_p 6449 : ℝ) = 25 := by exact_mod_cast BSD_ap_p6449
  have key : r ^ 2 - (a_p 6449 : ℝ) * r + ((6449 : ℕ) : ℝ) =
      (r - 25/2) ^ 2 + 25171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (25 : ℝ)/2)]

-- p=6451: a_p=-12, 4p-a_p²=25660
theorem BSD_DegreeNonneg_p6451 : BSD_FrobeniusDegreeNonneg_OPEN 6451 := fun r => by
  have hap : (a_p 6451 : ℝ) = -12 := by exact_mod_cast BSD_ap_p6451
  have key : r ^ 2 - (a_p 6451 : ℝ) * r + ((6451 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 25660/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6361 : BSD_Hasse_OPEN 6361 :=
  BSD_hasse_of_degree_nonneg 6361 BSD_DegreeNonneg_p6361
theorem BSD_Hasse_OPEN_p6367 : BSD_Hasse_OPEN 6367 :=
  BSD_hasse_of_degree_nonneg 6367 BSD_DegreeNonneg_p6367
theorem BSD_Hasse_OPEN_p6373 : BSD_Hasse_OPEN 6373 :=
  BSD_hasse_of_degree_nonneg 6373 BSD_DegreeNonneg_p6373
theorem BSD_Hasse_OPEN_p6379 : BSD_Hasse_OPEN 6379 :=
  BSD_hasse_of_degree_nonneg 6379 BSD_DegreeNonneg_p6379
theorem BSD_Hasse_OPEN_p6389 : BSD_Hasse_OPEN 6389 :=
  BSD_hasse_of_degree_nonneg 6389 BSD_DegreeNonneg_p6389
theorem BSD_Hasse_OPEN_p6397 : BSD_Hasse_OPEN 6397 :=
  BSD_hasse_of_degree_nonneg 6397 BSD_DegreeNonneg_p6397
theorem BSD_Hasse_OPEN_p6421 : BSD_Hasse_OPEN 6421 :=
  BSD_hasse_of_degree_nonneg 6421 BSD_DegreeNonneg_p6421
theorem BSD_Hasse_OPEN_p6427 : BSD_Hasse_OPEN 6427 :=
  BSD_hasse_of_degree_nonneg 6427 BSD_DegreeNonneg_p6427
theorem BSD_Hasse_OPEN_p6449 : BSD_Hasse_OPEN 6449 :=
  BSD_hasse_of_degree_nonneg 6449 BSD_DegreeNonneg_p6449
theorem BSD_Hasse_OPEN_p6451 : BSD_Hasse_OPEN 6451 :=
  BSD_hasse_of_degree_nonneg 6451 BSD_DegreeNonneg_p6451

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6361 : (a_p 6361 : ℝ) ^ 2 ≤ 4 * (6361 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6361
theorem BSD_HasseBound_Disc_p6367 : (a_p 6367 : ℝ) ^ 2 ≤ 4 * (6367 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6367
theorem BSD_HasseBound_Disc_p6373 : (a_p 6373 : ℝ) ^ 2 ≤ 4 * (6373 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6373
theorem BSD_HasseBound_Disc_p6379 : (a_p 6379 : ℝ) ^ 2 ≤ 4 * (6379 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6379
theorem BSD_HasseBound_Disc_p6389 : (a_p 6389 : ℝ) ^ 2 ≤ 4 * (6389 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6389
theorem BSD_HasseBound_Disc_p6397 : (a_p 6397 : ℝ) ^ 2 ≤ 4 * (6397 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6397
theorem BSD_HasseBound_Disc_p6421 : (a_p 6421 : ℝ) ^ 2 ≤ 4 * (6421 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6421
theorem BSD_HasseBound_Disc_p6427 : (a_p 6427 : ℝ) ^ 2 ≤ 4 * (6427 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6427
theorem BSD_HasseBound_Disc_p6449 : (a_p 6449 : ℝ) ^ 2 ≤ 4 * (6449 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6449
theorem BSD_HasseBound_Disc_p6451 : (a_p 6451 : ℝ) ^ 2 ≤ 4 * (6451 : ℝ) :=
  BSD_disc_from_deg_849 BSD_DegreeNonneg_p6451

end Towers.BSD