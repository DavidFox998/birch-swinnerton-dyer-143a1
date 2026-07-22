/-
================================================================
Towers / BSD / BSD_Genesis861_CLOSED  (genesis-861)

HasseBridge Tier C: Hasse bounds for primes
7489..7549 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7489: card=7481, a_p=+9, disc=-29875
  p=7499: card=7484, a_p=+16, disc=-29740
  p=7507: card=7437, a_p=+71, disc=-24987
  p=7517: card=7608, a_p=-90, disc=-21968
  p=7523: card=7370, a_p=+154, disc=-6376
  p=7529: card=7503, a_p=+27, disc=-29387
  p=7537: card=7484, a_p=+54, disc=-27232
  p=7541: card=7574, a_p=-32, disc=-29140
  p=7547: card=7547, a_p=+1, disc=-30187
  p=7549: card=7551, a_p=-1, disc=-30195

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_861 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i861_p7489 : Fact (7489 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7499 : Fact (7499 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7507 : Fact (7507 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7517 : Fact (7517 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7523 : Fact (7523 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7529 : Fact (7529 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7537 : Fact (7537 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7541 : Fact (7541 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7547 : Fact (7547 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7549 : Fact (7549 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7489 : (E143_Finset 7489).card = 7481 := by native_decide
theorem BSD_E143_card_p7499 : (E143_Finset 7499).card = 7484 := by native_decide
theorem BSD_E143_card_p7507 : (E143_Finset 7507).card = 7437 := by native_decide
theorem BSD_E143_card_p7517 : (E143_Finset 7517).card = 7608 := by native_decide
theorem BSD_E143_card_p7523 : (E143_Finset 7523).card = 7370 := by native_decide
theorem BSD_E143_card_p7529 : (E143_Finset 7529).card = 7503 := by native_decide
theorem BSD_E143_card_p7537 : (E143_Finset 7537).card = 7484 := by native_decide
theorem BSD_E143_card_p7541 : (E143_Finset 7541).card = 7574 := by native_decide
theorem BSD_E143_card_p7547 : (E143_Finset 7547).card = 7547 := by native_decide
theorem BSD_E143_card_p7549 : (E143_Finset 7549).card = 7551 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7489 : a_p 7489 = (9 : ℤ) := by
  have h := BSD_E143_card_p7489; unfold a_p; omega
theorem BSD_ap_p7499 : a_p 7499 = (16 : ℤ) := by
  have h := BSD_E143_card_p7499; unfold a_p; omega
theorem BSD_ap_p7507 : a_p 7507 = (71 : ℤ) := by
  have h := BSD_E143_card_p7507; unfold a_p; omega
theorem BSD_ap_p7517 : a_p 7517 = (-90 : ℤ) := by
  have h := BSD_E143_card_p7517; unfold a_p; omega
theorem BSD_ap_p7523 : a_p 7523 = (154 : ℤ) := by
  have h := BSD_E143_card_p7523; unfold a_p; omega
theorem BSD_ap_p7529 : a_p 7529 = (27 : ℤ) := by
  have h := BSD_E143_card_p7529; unfold a_p; omega
theorem BSD_ap_p7537 : a_p 7537 = (54 : ℤ) := by
  have h := BSD_E143_card_p7537; unfold a_p; omega
theorem BSD_ap_p7541 : a_p 7541 = (-32 : ℤ) := by
  have h := BSD_E143_card_p7541; unfold a_p; omega
theorem BSD_ap_p7547 : a_p 7547 = (1 : ℤ) := by
  have h := BSD_E143_card_p7547; unfold a_p; omega
theorem BSD_ap_p7549 : a_p 7549 = (-1 : ℤ) := by
  have h := BSD_E143_card_p7549; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7489: a_p=+9, 4p-a_p²=29875
theorem BSD_DegreeNonneg_p7489 : BSD_FrobeniusDegreeNonneg_OPEN 7489 := fun r => by
  have hap : (a_p 7489 : ℝ) = 9 := by exact_mod_cast BSD_ap_p7489
  have key : r ^ 2 - (a_p 7489 : ℝ) * r + ((7489 : ℕ) : ℝ) =
      (r - 9/2) ^ 2 + 29875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (9 : ℝ)/2)]

-- p=7499: a_p=+16, 4p-a_p²=29740
theorem BSD_DegreeNonneg_p7499 : BSD_FrobeniusDegreeNonneg_OPEN 7499 := fun r => by
  have hap : (a_p 7499 : ℝ) = 16 := by exact_mod_cast BSD_ap_p7499
  have key : r ^ 2 - (a_p 7499 : ℝ) * r + ((7499 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 29740/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

-- p=7507: a_p=+71, 4p-a_p²=24987
theorem BSD_DegreeNonneg_p7507 : BSD_FrobeniusDegreeNonneg_OPEN 7507 := fun r => by
  have hap : (a_p 7507 : ℝ) = 71 := by exact_mod_cast BSD_ap_p7507
  have key : r ^ 2 - (a_p 7507 : ℝ) * r + ((7507 : ℕ) : ℝ) =
      (r - 71/2) ^ 2 + 24987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (71 : ℝ)/2)]

-- p=7517: a_p=-90, 4p-a_p²=21968
theorem BSD_DegreeNonneg_p7517 : BSD_FrobeniusDegreeNonneg_OPEN 7517 := fun r => by
  have hap : (a_p 7517 : ℝ) = -90 := by exact_mod_cast BSD_ap_p7517
  have key : r ^ 2 - (a_p 7517 : ℝ) * r + ((7517 : ℕ) : ℝ) =
      (r + 90/2) ^ 2 + 21968/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (90 : ℝ)/2)]

-- p=7523: a_p=+154, 4p-a_p²=6376
theorem BSD_DegreeNonneg_p7523 : BSD_FrobeniusDegreeNonneg_OPEN 7523 := fun r => by
  have hap : (a_p 7523 : ℝ) = 154 := by exact_mod_cast BSD_ap_p7523
  have key : r ^ 2 - (a_p 7523 : ℝ) * r + ((7523 : ℕ) : ℝ) =
      (r - 154/2) ^ 2 + 6376/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (154 : ℝ)/2)]

-- p=7529: a_p=+27, 4p-a_p²=29387
theorem BSD_DegreeNonneg_p7529 : BSD_FrobeniusDegreeNonneg_OPEN 7529 := fun r => by
  have hap : (a_p 7529 : ℝ) = 27 := by exact_mod_cast BSD_ap_p7529
  have key : r ^ 2 - (a_p 7529 : ℝ) * r + ((7529 : ℕ) : ℝ) =
      (r - 27/2) ^ 2 + 29387/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (27 : ℝ)/2)]

-- p=7537: a_p=+54, 4p-a_p²=27232
theorem BSD_DegreeNonneg_p7537 : BSD_FrobeniusDegreeNonneg_OPEN 7537 := fun r => by
  have hap : (a_p 7537 : ℝ) = 54 := by exact_mod_cast BSD_ap_p7537
  have key : r ^ 2 - (a_p 7537 : ℝ) * r + ((7537 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 27232/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

-- p=7541: a_p=-32, 4p-a_p²=29140
theorem BSD_DegreeNonneg_p7541 : BSD_FrobeniusDegreeNonneg_OPEN 7541 := fun r => by
  have hap : (a_p 7541 : ℝ) = -32 := by exact_mod_cast BSD_ap_p7541
  have key : r ^ 2 - (a_p 7541 : ℝ) * r + ((7541 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 29140/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=7547: a_p=+1, 4p-a_p²=30187
theorem BSD_DegreeNonneg_p7547 : BSD_FrobeniusDegreeNonneg_OPEN 7547 := fun r => by
  have hap : (a_p 7547 : ℝ) = 1 := by exact_mod_cast BSD_ap_p7547
  have key : r ^ 2 - (a_p 7547 : ℝ) * r + ((7547 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 30187/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

-- p=7549: a_p=-1, 4p-a_p²=30195
theorem BSD_DegreeNonneg_p7549 : BSD_FrobeniusDegreeNonneg_OPEN 7549 := fun r => by
  have hap : (a_p 7549 : ℝ) = -1 := by exact_mod_cast BSD_ap_p7549
  have key : r ^ 2 - (a_p 7549 : ℝ) * r + ((7549 : ℕ) : ℝ) =
      (r + 1/2) ^ 2 + 30195/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (1 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7489 : BSD_Hasse_OPEN 7489 :=
  BSD_hasse_of_degree_nonneg 7489 BSD_DegreeNonneg_p7489
theorem BSD_Hasse_OPEN_p7499 : BSD_Hasse_OPEN 7499 :=
  BSD_hasse_of_degree_nonneg 7499 BSD_DegreeNonneg_p7499
theorem BSD_Hasse_OPEN_p7507 : BSD_Hasse_OPEN 7507 :=
  BSD_hasse_of_degree_nonneg 7507 BSD_DegreeNonneg_p7507
theorem BSD_Hasse_OPEN_p7517 : BSD_Hasse_OPEN 7517 :=
  BSD_hasse_of_degree_nonneg 7517 BSD_DegreeNonneg_p7517
theorem BSD_Hasse_OPEN_p7523 : BSD_Hasse_OPEN 7523 :=
  BSD_hasse_of_degree_nonneg 7523 BSD_DegreeNonneg_p7523
theorem BSD_Hasse_OPEN_p7529 : BSD_Hasse_OPEN 7529 :=
  BSD_hasse_of_degree_nonneg 7529 BSD_DegreeNonneg_p7529
theorem BSD_Hasse_OPEN_p7537 : BSD_Hasse_OPEN 7537 :=
  BSD_hasse_of_degree_nonneg 7537 BSD_DegreeNonneg_p7537
theorem BSD_Hasse_OPEN_p7541 : BSD_Hasse_OPEN 7541 :=
  BSD_hasse_of_degree_nonneg 7541 BSD_DegreeNonneg_p7541
theorem BSD_Hasse_OPEN_p7547 : BSD_Hasse_OPEN 7547 :=
  BSD_hasse_of_degree_nonneg 7547 BSD_DegreeNonneg_p7547
theorem BSD_Hasse_OPEN_p7549 : BSD_Hasse_OPEN 7549 :=
  BSD_hasse_of_degree_nonneg 7549 BSD_DegreeNonneg_p7549

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7489 : (a_p 7489 : ℝ) ^ 2 ≤ 4 * (7489 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7489
theorem BSD_HasseBound_Disc_p7499 : (a_p 7499 : ℝ) ^ 2 ≤ 4 * (7499 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7499
theorem BSD_HasseBound_Disc_p7507 : (a_p 7507 : ℝ) ^ 2 ≤ 4 * (7507 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7507
theorem BSD_HasseBound_Disc_p7517 : (a_p 7517 : ℝ) ^ 2 ≤ 4 * (7517 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7517
theorem BSD_HasseBound_Disc_p7523 : (a_p 7523 : ℝ) ^ 2 ≤ 4 * (7523 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7523
theorem BSD_HasseBound_Disc_p7529 : (a_p 7529 : ℝ) ^ 2 ≤ 4 * (7529 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7529
theorem BSD_HasseBound_Disc_p7537 : (a_p 7537 : ℝ) ^ 2 ≤ 4 * (7537 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7537
theorem BSD_HasseBound_Disc_p7541 : (a_p 7541 : ℝ) ^ 2 ≤ 4 * (7541 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7541
theorem BSD_HasseBound_Disc_p7547 : (a_p 7547 : ℝ) ^ 2 ≤ 4 * (7547 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7547
theorem BSD_HasseBound_Disc_p7549 : (a_p 7549 : ℝ) ^ 2 ≤ 4 * (7549 : ℝ) :=
  BSD_disc_from_deg_861 BSD_DegreeNonneg_p7549

end Towers.BSD