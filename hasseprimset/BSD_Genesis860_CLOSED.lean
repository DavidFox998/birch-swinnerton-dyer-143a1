/-
================================================================
Towers / BSD / BSD_Genesis860_CLOSED  (genesis-860)

HasseBridge Tier C: Hasse bounds for primes
7393..7487 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7393: card=7541, a_p=-147, disc=-7963
  p=7411: card=7296, a_p=+116, disc=-16188
  p=7417: card=7421, a_p=-3, disc=-29659
  p=7433: card=7566, a_p=-132, disc=-12308
  p=7451: card=7608, a_p=-156, disc=-5468
  p=7457: card=7408, a_p=+50, disc=-27328
  p=7459: card=7581, a_p=-121, disc=-15195
  p=7477: card=7528, a_p=-50, disc=-27408
  p=7481: card=7611, a_p=-129, disc=-13283
  p=7487: card=7590, a_p=-102, disc=-19544

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_860 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i860_p7393 : Fact (7393 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7411 : Fact (7411 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7417 : Fact (7417 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7433 : Fact (7433 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7451 : Fact (7451 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7457 : Fact (7457 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7459 : Fact (7459 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7477 : Fact (7477 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7481 : Fact (7481 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7487 : Fact (7487 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7393 : (E143_Finset 7393).card = 7541 := by native_decide
theorem BSD_E143_card_p7411 : (E143_Finset 7411).card = 7296 := by native_decide
theorem BSD_E143_card_p7417 : (E143_Finset 7417).card = 7421 := by native_decide
theorem BSD_E143_card_p7433 : (E143_Finset 7433).card = 7566 := by native_decide
theorem BSD_E143_card_p7451 : (E143_Finset 7451).card = 7608 := by native_decide
theorem BSD_E143_card_p7457 : (E143_Finset 7457).card = 7408 := by native_decide
theorem BSD_E143_card_p7459 : (E143_Finset 7459).card = 7581 := by native_decide
theorem BSD_E143_card_p7477 : (E143_Finset 7477).card = 7528 := by native_decide
theorem BSD_E143_card_p7481 : (E143_Finset 7481).card = 7611 := by native_decide
theorem BSD_E143_card_p7487 : (E143_Finset 7487).card = 7590 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7393 : a_p 7393 = (-147 : ℤ) := by
  have h := BSD_E143_card_p7393; unfold a_p; omega
theorem BSD_ap_p7411 : a_p 7411 = (116 : ℤ) := by
  have h := BSD_E143_card_p7411; unfold a_p; omega
theorem BSD_ap_p7417 : a_p 7417 = (-3 : ℤ) := by
  have h := BSD_E143_card_p7417; unfold a_p; omega
theorem BSD_ap_p7433 : a_p 7433 = (-132 : ℤ) := by
  have h := BSD_E143_card_p7433; unfold a_p; omega
theorem BSD_ap_p7451 : a_p 7451 = (-156 : ℤ) := by
  have h := BSD_E143_card_p7451; unfold a_p; omega
theorem BSD_ap_p7457 : a_p 7457 = (50 : ℤ) := by
  have h := BSD_E143_card_p7457; unfold a_p; omega
theorem BSD_ap_p7459 : a_p 7459 = (-121 : ℤ) := by
  have h := BSD_E143_card_p7459; unfold a_p; omega
theorem BSD_ap_p7477 : a_p 7477 = (-50 : ℤ) := by
  have h := BSD_E143_card_p7477; unfold a_p; omega
theorem BSD_ap_p7481 : a_p 7481 = (-129 : ℤ) := by
  have h := BSD_E143_card_p7481; unfold a_p; omega
theorem BSD_ap_p7487 : a_p 7487 = (-102 : ℤ) := by
  have h := BSD_E143_card_p7487; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7393: a_p=-147, 4p-a_p²=7963
theorem BSD_DegreeNonneg_p7393 : BSD_FrobeniusDegreeNonneg_OPEN 7393 := fun r => by
  have hap : (a_p 7393 : ℝ) = -147 := by exact_mod_cast BSD_ap_p7393
  have key : r ^ 2 - (a_p 7393 : ℝ) * r + ((7393 : ℕ) : ℝ) =
      (r + 147/2) ^ 2 + 7963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (147 : ℝ)/2)]

-- p=7411: a_p=+116, 4p-a_p²=16188
theorem BSD_DegreeNonneg_p7411 : BSD_FrobeniusDegreeNonneg_OPEN 7411 := fun r => by
  have hap : (a_p 7411 : ℝ) = 116 := by exact_mod_cast BSD_ap_p7411
  have key : r ^ 2 - (a_p 7411 : ℝ) * r + ((7411 : ℕ) : ℝ) =
      (r - 116/2) ^ 2 + 16188/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (116 : ℝ)/2)]

-- p=7417: a_p=-3, 4p-a_p²=29659
theorem BSD_DegreeNonneg_p7417 : BSD_FrobeniusDegreeNonneg_OPEN 7417 := fun r => by
  have hap : (a_p 7417 : ℝ) = -3 := by exact_mod_cast BSD_ap_p7417
  have key : r ^ 2 - (a_p 7417 : ℝ) * r + ((7417 : ℕ) : ℝ) =
      (r + 3/2) ^ 2 + 29659/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (3 : ℝ)/2)]

-- p=7433: a_p=-132, 4p-a_p²=12308
theorem BSD_DegreeNonneg_p7433 : BSD_FrobeniusDegreeNonneg_OPEN 7433 := fun r => by
  have hap : (a_p 7433 : ℝ) = -132 := by exact_mod_cast BSD_ap_p7433
  have key : r ^ 2 - (a_p 7433 : ℝ) * r + ((7433 : ℕ) : ℝ) =
      (r + 132/2) ^ 2 + 12308/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (132 : ℝ)/2)]

-- p=7451: a_p=-156, 4p-a_p²=5468
theorem BSD_DegreeNonneg_p7451 : BSD_FrobeniusDegreeNonneg_OPEN 7451 := fun r => by
  have hap : (a_p 7451 : ℝ) = -156 := by exact_mod_cast BSD_ap_p7451
  have key : r ^ 2 - (a_p 7451 : ℝ) * r + ((7451 : ℕ) : ℝ) =
      (r + 156/2) ^ 2 + 5468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (156 : ℝ)/2)]

-- p=7457: a_p=+50, 4p-a_p²=27328
theorem BSD_DegreeNonneg_p7457 : BSD_FrobeniusDegreeNonneg_OPEN 7457 := fun r => by
  have hap : (a_p 7457 : ℝ) = 50 := by exact_mod_cast BSD_ap_p7457
  have key : r ^ 2 - (a_p 7457 : ℝ) * r + ((7457 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 27328/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

-- p=7459: a_p=-121, 4p-a_p²=15195
theorem BSD_DegreeNonneg_p7459 : BSD_FrobeniusDegreeNonneg_OPEN 7459 := fun r => by
  have hap : (a_p 7459 : ℝ) = -121 := by exact_mod_cast BSD_ap_p7459
  have key : r ^ 2 - (a_p 7459 : ℝ) * r + ((7459 : ℕ) : ℝ) =
      (r + 121/2) ^ 2 + 15195/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (121 : ℝ)/2)]

-- p=7477: a_p=-50, 4p-a_p²=27408
theorem BSD_DegreeNonneg_p7477 : BSD_FrobeniusDegreeNonneg_OPEN 7477 := fun r => by
  have hap : (a_p 7477 : ℝ) = -50 := by exact_mod_cast BSD_ap_p7477
  have key : r ^ 2 - (a_p 7477 : ℝ) * r + ((7477 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 27408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

-- p=7481: a_p=-129, 4p-a_p²=13283
theorem BSD_DegreeNonneg_p7481 : BSD_FrobeniusDegreeNonneg_OPEN 7481 := fun r => by
  have hap : (a_p 7481 : ℝ) = -129 := by exact_mod_cast BSD_ap_p7481
  have key : r ^ 2 - (a_p 7481 : ℝ) * r + ((7481 : ℕ) : ℝ) =
      (r + 129/2) ^ 2 + 13283/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (129 : ℝ)/2)]

-- p=7487: a_p=-102, 4p-a_p²=19544
theorem BSD_DegreeNonneg_p7487 : BSD_FrobeniusDegreeNonneg_OPEN 7487 := fun r => by
  have hap : (a_p 7487 : ℝ) = -102 := by exact_mod_cast BSD_ap_p7487
  have key : r ^ 2 - (a_p 7487 : ℝ) * r + ((7487 : ℕ) : ℝ) =
      (r + 102/2) ^ 2 + 19544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (102 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7393 : BSD_Hasse_OPEN 7393 :=
  BSD_hasse_of_degree_nonneg 7393 BSD_DegreeNonneg_p7393
theorem BSD_Hasse_OPEN_p7411 : BSD_Hasse_OPEN 7411 :=
  BSD_hasse_of_degree_nonneg 7411 BSD_DegreeNonneg_p7411
theorem BSD_Hasse_OPEN_p7417 : BSD_Hasse_OPEN 7417 :=
  BSD_hasse_of_degree_nonneg 7417 BSD_DegreeNonneg_p7417
theorem BSD_Hasse_OPEN_p7433 : BSD_Hasse_OPEN 7433 :=
  BSD_hasse_of_degree_nonneg 7433 BSD_DegreeNonneg_p7433
theorem BSD_Hasse_OPEN_p7451 : BSD_Hasse_OPEN 7451 :=
  BSD_hasse_of_degree_nonneg 7451 BSD_DegreeNonneg_p7451
theorem BSD_Hasse_OPEN_p7457 : BSD_Hasse_OPEN 7457 :=
  BSD_hasse_of_degree_nonneg 7457 BSD_DegreeNonneg_p7457
theorem BSD_Hasse_OPEN_p7459 : BSD_Hasse_OPEN 7459 :=
  BSD_hasse_of_degree_nonneg 7459 BSD_DegreeNonneg_p7459
theorem BSD_Hasse_OPEN_p7477 : BSD_Hasse_OPEN 7477 :=
  BSD_hasse_of_degree_nonneg 7477 BSD_DegreeNonneg_p7477
theorem BSD_Hasse_OPEN_p7481 : BSD_Hasse_OPEN 7481 :=
  BSD_hasse_of_degree_nonneg 7481 BSD_DegreeNonneg_p7481
theorem BSD_Hasse_OPEN_p7487 : BSD_Hasse_OPEN 7487 :=
  BSD_hasse_of_degree_nonneg 7487 BSD_DegreeNonneg_p7487

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7393 : (a_p 7393 : ℝ) ^ 2 ≤ 4 * (7393 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7393
theorem BSD_HasseBound_Disc_p7411 : (a_p 7411 : ℝ) ^ 2 ≤ 4 * (7411 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7411
theorem BSD_HasseBound_Disc_p7417 : (a_p 7417 : ℝ) ^ 2 ≤ 4 * (7417 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7417
theorem BSD_HasseBound_Disc_p7433 : (a_p 7433 : ℝ) ^ 2 ≤ 4 * (7433 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7433
theorem BSD_HasseBound_Disc_p7451 : (a_p 7451 : ℝ) ^ 2 ≤ 4 * (7451 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7451
theorem BSD_HasseBound_Disc_p7457 : (a_p 7457 : ℝ) ^ 2 ≤ 4 * (7457 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7457
theorem BSD_HasseBound_Disc_p7459 : (a_p 7459 : ℝ) ^ 2 ≤ 4 * (7459 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7459
theorem BSD_HasseBound_Disc_p7477 : (a_p 7477 : ℝ) ^ 2 ≤ 4 * (7477 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7477
theorem BSD_HasseBound_Disc_p7481 : (a_p 7481 : ℝ) ^ 2 ≤ 4 * (7481 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7481
theorem BSD_HasseBound_Disc_p7487 : (a_p 7487 : ℝ) ^ 2 ≤ 4 * (7487 : ℝ) :=
  BSD_disc_from_deg_860 BSD_DegreeNonneg_p7487

end Towers.BSD