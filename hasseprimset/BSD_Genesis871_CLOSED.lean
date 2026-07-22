/-
================================================================
Towers / BSD / BSD_Genesis871_CLOSED  (genesis-871)

HasseBridge Tier C: Hasse bounds for primes
8377..8461 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8377: card=8440, a_p=-62, disc=-29664
  p=8387: card=8400, a_p=-12, disc=-33404
  p=8389: card=8498, a_p=-108, disc=-21892
  p=8419: card=8284, a_p=+136, disc=-15180
  p=8423: card=8476, a_p=-52, disc=-30988
  p=8429: card=8491, a_p=-61, disc=-29995
  p=8431: card=8415, a_p=+17, disc=-33435
  p=8443: card=8328, a_p=+116, disc=-20316
  p=8447: card=8438, a_p=+10, disc=-33688
  p=8461: card=8638, a_p=-176, disc=-2868

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_871 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i871_p8377 : Fact (8377 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8387 : Fact (8387 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8389 : Fact (8389 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8419 : Fact (8419 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8423 : Fact (8423 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8429 : Fact (8429 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8431 : Fact (8431 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8443 : Fact (8443 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8447 : Fact (8447 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8461 : Fact (8461 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8377 : (E143_Finset 8377).card = 8440 := by native_decide
theorem BSD_E143_card_p8387 : (E143_Finset 8387).card = 8400 := by native_decide
theorem BSD_E143_card_p8389 : (E143_Finset 8389).card = 8498 := by native_decide
theorem BSD_E143_card_p8419 : (E143_Finset 8419).card = 8284 := by native_decide
theorem BSD_E143_card_p8423 : (E143_Finset 8423).card = 8476 := by native_decide
theorem BSD_E143_card_p8429 : (E143_Finset 8429).card = 8491 := by native_decide
theorem BSD_E143_card_p8431 : (E143_Finset 8431).card = 8415 := by native_decide
theorem BSD_E143_card_p8443 : (E143_Finset 8443).card = 8328 := by native_decide
theorem BSD_E143_card_p8447 : (E143_Finset 8447).card = 8438 := by native_decide
theorem BSD_E143_card_p8461 : (E143_Finset 8461).card = 8638 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8377 : a_p 8377 = (-62 : ℤ) := by
  have h := BSD_E143_card_p8377; unfold a_p; omega
theorem BSD_ap_p8387 : a_p 8387 = (-12 : ℤ) := by
  have h := BSD_E143_card_p8387; unfold a_p; omega
theorem BSD_ap_p8389 : a_p 8389 = (-108 : ℤ) := by
  have h := BSD_E143_card_p8389; unfold a_p; omega
theorem BSD_ap_p8419 : a_p 8419 = (136 : ℤ) := by
  have h := BSD_E143_card_p8419; unfold a_p; omega
theorem BSD_ap_p8423 : a_p 8423 = (-52 : ℤ) := by
  have h := BSD_E143_card_p8423; unfold a_p; omega
theorem BSD_ap_p8429 : a_p 8429 = (-61 : ℤ) := by
  have h := BSD_E143_card_p8429; unfold a_p; omega
theorem BSD_ap_p8431 : a_p 8431 = (17 : ℤ) := by
  have h := BSD_E143_card_p8431; unfold a_p; omega
theorem BSD_ap_p8443 : a_p 8443 = (116 : ℤ) := by
  have h := BSD_E143_card_p8443; unfold a_p; omega
theorem BSD_ap_p8447 : a_p 8447 = (10 : ℤ) := by
  have h := BSD_E143_card_p8447; unfold a_p; omega
theorem BSD_ap_p8461 : a_p 8461 = (-176 : ℤ) := by
  have h := BSD_E143_card_p8461; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8377: a_p=-62, 4p-a_p²=29664
theorem BSD_DegreeNonneg_p8377 : BSD_FrobeniusDegreeNonneg_OPEN 8377 := fun r => by
  have hap : (a_p 8377 : ℝ) = -62 := by exact_mod_cast BSD_ap_p8377
  have key : r ^ 2 - (a_p 8377 : ℝ) * r + ((8377 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 29664/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

-- p=8387: a_p=-12, 4p-a_p²=33404
theorem BSD_DegreeNonneg_p8387 : BSD_FrobeniusDegreeNonneg_OPEN 8387 := fun r => by
  have hap : (a_p 8387 : ℝ) = -12 := by exact_mod_cast BSD_ap_p8387
  have key : r ^ 2 - (a_p 8387 : ℝ) * r + ((8387 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 33404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

-- p=8389: a_p=-108, 4p-a_p²=21892
theorem BSD_DegreeNonneg_p8389 : BSD_FrobeniusDegreeNonneg_OPEN 8389 := fun r => by
  have hap : (a_p 8389 : ℝ) = -108 := by exact_mod_cast BSD_ap_p8389
  have key : r ^ 2 - (a_p 8389 : ℝ) * r + ((8389 : ℕ) : ℝ) =
      (r + 108/2) ^ 2 + 21892/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (108 : ℝ)/2)]

-- p=8419: a_p=+136, 4p-a_p²=15180
theorem BSD_DegreeNonneg_p8419 : BSD_FrobeniusDegreeNonneg_OPEN 8419 := fun r => by
  have hap : (a_p 8419 : ℝ) = 136 := by exact_mod_cast BSD_ap_p8419
  have key : r ^ 2 - (a_p 8419 : ℝ) * r + ((8419 : ℕ) : ℝ) =
      (r - 136/2) ^ 2 + 15180/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (136 : ℝ)/2)]

-- p=8423: a_p=-52, 4p-a_p²=30988
theorem BSD_DegreeNonneg_p8423 : BSD_FrobeniusDegreeNonneg_OPEN 8423 := fun r => by
  have hap : (a_p 8423 : ℝ) = -52 := by exact_mod_cast BSD_ap_p8423
  have key : r ^ 2 - (a_p 8423 : ℝ) * r + ((8423 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 30988/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

-- p=8429: a_p=-61, 4p-a_p²=29995
theorem BSD_DegreeNonneg_p8429 : BSD_FrobeniusDegreeNonneg_OPEN 8429 := fun r => by
  have hap : (a_p 8429 : ℝ) = -61 := by exact_mod_cast BSD_ap_p8429
  have key : r ^ 2 - (a_p 8429 : ℝ) * r + ((8429 : ℕ) : ℝ) =
      (r + 61/2) ^ 2 + 29995/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (61 : ℝ)/2)]

-- p=8431: a_p=+17, 4p-a_p²=33435
theorem BSD_DegreeNonneg_p8431 : BSD_FrobeniusDegreeNonneg_OPEN 8431 := fun r => by
  have hap : (a_p 8431 : ℝ) = 17 := by exact_mod_cast BSD_ap_p8431
  have key : r ^ 2 - (a_p 8431 : ℝ) * r + ((8431 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 33435/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

-- p=8443: a_p=+116, 4p-a_p²=20316
theorem BSD_DegreeNonneg_p8443 : BSD_FrobeniusDegreeNonneg_OPEN 8443 := fun r => by
  have hap : (a_p 8443 : ℝ) = 116 := by exact_mod_cast BSD_ap_p8443
  have key : r ^ 2 - (a_p 8443 : ℝ) * r + ((8443 : ℕ) : ℝ) =
      (r - 116/2) ^ 2 + 20316/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (116 : ℝ)/2)]

-- p=8447: a_p=+10, 4p-a_p²=33688
theorem BSD_DegreeNonneg_p8447 : BSD_FrobeniusDegreeNonneg_OPEN 8447 := fun r => by
  have hap : (a_p 8447 : ℝ) = 10 := by exact_mod_cast BSD_ap_p8447
  have key : r ^ 2 - (a_p 8447 : ℝ) * r + ((8447 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 33688/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

-- p=8461: a_p=-176, 4p-a_p²=2868
theorem BSD_DegreeNonneg_p8461 : BSD_FrobeniusDegreeNonneg_OPEN 8461 := fun r => by
  have hap : (a_p 8461 : ℝ) = -176 := by exact_mod_cast BSD_ap_p8461
  have key : r ^ 2 - (a_p 8461 : ℝ) * r + ((8461 : ℕ) : ℝ) =
      (r + 176/2) ^ 2 + 2868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (176 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8377 : BSD_Hasse_OPEN 8377 :=
  BSD_hasse_of_degree_nonneg 8377 BSD_DegreeNonneg_p8377
theorem BSD_Hasse_OPEN_p8387 : BSD_Hasse_OPEN 8387 :=
  BSD_hasse_of_degree_nonneg 8387 BSD_DegreeNonneg_p8387
theorem BSD_Hasse_OPEN_p8389 : BSD_Hasse_OPEN 8389 :=
  BSD_hasse_of_degree_nonneg 8389 BSD_DegreeNonneg_p8389
theorem BSD_Hasse_OPEN_p8419 : BSD_Hasse_OPEN 8419 :=
  BSD_hasse_of_degree_nonneg 8419 BSD_DegreeNonneg_p8419
theorem BSD_Hasse_OPEN_p8423 : BSD_Hasse_OPEN 8423 :=
  BSD_hasse_of_degree_nonneg 8423 BSD_DegreeNonneg_p8423
theorem BSD_Hasse_OPEN_p8429 : BSD_Hasse_OPEN 8429 :=
  BSD_hasse_of_degree_nonneg 8429 BSD_DegreeNonneg_p8429
theorem BSD_Hasse_OPEN_p8431 : BSD_Hasse_OPEN 8431 :=
  BSD_hasse_of_degree_nonneg 8431 BSD_DegreeNonneg_p8431
theorem BSD_Hasse_OPEN_p8443 : BSD_Hasse_OPEN 8443 :=
  BSD_hasse_of_degree_nonneg 8443 BSD_DegreeNonneg_p8443
theorem BSD_Hasse_OPEN_p8447 : BSD_Hasse_OPEN 8447 :=
  BSD_hasse_of_degree_nonneg 8447 BSD_DegreeNonneg_p8447
theorem BSD_Hasse_OPEN_p8461 : BSD_Hasse_OPEN 8461 :=
  BSD_hasse_of_degree_nonneg 8461 BSD_DegreeNonneg_p8461

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8377 : (a_p 8377 : ℝ) ^ 2 ≤ 4 * (8377 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8377
theorem BSD_HasseBound_Disc_p8387 : (a_p 8387 : ℝ) ^ 2 ≤ 4 * (8387 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8387
theorem BSD_HasseBound_Disc_p8389 : (a_p 8389 : ℝ) ^ 2 ≤ 4 * (8389 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8389
theorem BSD_HasseBound_Disc_p8419 : (a_p 8419 : ℝ) ^ 2 ≤ 4 * (8419 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8419
theorem BSD_HasseBound_Disc_p8423 : (a_p 8423 : ℝ) ^ 2 ≤ 4 * (8423 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8423
theorem BSD_HasseBound_Disc_p8429 : (a_p 8429 : ℝ) ^ 2 ≤ 4 * (8429 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8429
theorem BSD_HasseBound_Disc_p8431 : (a_p 8431 : ℝ) ^ 2 ≤ 4 * (8431 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8431
theorem BSD_HasseBound_Disc_p8443 : (a_p 8443 : ℝ) ^ 2 ≤ 4 * (8443 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8443
theorem BSD_HasseBound_Disc_p8447 : (a_p 8447 : ℝ) ^ 2 ≤ 4 * (8447 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8447
theorem BSD_HasseBound_Disc_p8461 : (a_p 8461 : ℝ) ^ 2 ≤ 4 * (8461 : ℝ) :=
  BSD_disc_from_deg_871 BSD_DegreeNonneg_p8461

end Towers.BSD