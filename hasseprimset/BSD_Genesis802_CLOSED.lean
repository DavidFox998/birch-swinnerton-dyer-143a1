/-
================================================================
Towers / BSD / BSD_Genesis802_CLOSED  (genesis-802)

HasseBridge Tier C: Hasse bounds for primes
2417..2503 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2417: card=2442, a_p=-24, disc=-9092
  p=2423: card=2349, a_p=+75, disc=-4067
  p=2437: card=2398, a_p=+40, disc=-8148
  p=2441: card=2424, a_p=+18, disc=-9440
  p=2447: card=2421, a_p=+27, disc=-9059
  p=2459: card=2368, a_p=+92, disc=-1372
  p=2467: card=2461, a_p=+7, disc=-9819
  p=2473: card=2461, a_p=+13, disc=-9723
  p=2477: card=2470, a_p=+8, disc=-9844
  p=2503: card=2516, a_p=-12, disc=-9868

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_802 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i802_p2417 : Fact (2417 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2423 : Fact (2423 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2437 : Fact (2437 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2441 : Fact (2441 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2447 : Fact (2447 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2459 : Fact (2459 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2467 : Fact (2467 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2473 : Fact (2473 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2477 : Fact (2477 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2503 : Fact (2503 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2417 : (E143_Finset 2417).card = 2442 := by native_decide
theorem BSD_E143_card_p2423 : (E143_Finset 2423).card = 2349 := by native_decide
theorem BSD_E143_card_p2437 : (E143_Finset 2437).card = 2398 := by native_decide
theorem BSD_E143_card_p2441 : (E143_Finset 2441).card = 2424 := by native_decide
theorem BSD_E143_card_p2447 : (E143_Finset 2447).card = 2421 := by native_decide
theorem BSD_E143_card_p2459 : (E143_Finset 2459).card = 2368 := by native_decide
theorem BSD_E143_card_p2467 : (E143_Finset 2467).card = 2461 := by native_decide
theorem BSD_E143_card_p2473 : (E143_Finset 2473).card = 2461 := by native_decide
theorem BSD_E143_card_p2477 : (E143_Finset 2477).card = 2470 := by native_decide
theorem BSD_E143_card_p2503 : (E143_Finset 2503).card = 2516 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2417 : a_p 2417 = (-24 : ℤ) := by
  have h := BSD_E143_card_p2417; unfold a_p; omega
theorem BSD_ap_p2423 : a_p 2423 = (75 : ℤ) := by
  have h := BSD_E143_card_p2423; unfold a_p; omega
theorem BSD_ap_p2437 : a_p 2437 = (40 : ℤ) := by
  have h := BSD_E143_card_p2437; unfold a_p; omega
theorem BSD_ap_p2441 : a_p 2441 = (18 : ℤ) := by
  have h := BSD_E143_card_p2441; unfold a_p; omega
theorem BSD_ap_p2447 : a_p 2447 = (27 : ℤ) := by
  have h := BSD_E143_card_p2447; unfold a_p; omega
theorem BSD_ap_p2459 : a_p 2459 = (92 : ℤ) := by
  have h := BSD_E143_card_p2459; unfold a_p; omega
theorem BSD_ap_p2467 : a_p 2467 = (7 : ℤ) := by
  have h := BSD_E143_card_p2467; unfold a_p; omega
theorem BSD_ap_p2473 : a_p 2473 = (13 : ℤ) := by
  have h := BSD_E143_card_p2473; unfold a_p; omega
theorem BSD_ap_p2477 : a_p 2477 = (8 : ℤ) := by
  have h := BSD_E143_card_p2477; unfold a_p; omega
theorem BSD_ap_p2503 : a_p 2503 = (-12 : ℤ) := by
  have h := BSD_E143_card_p2503; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2417: a_p=-24, 4p-a_p²=9092
theorem BSD_DegreeNonneg_p2417 : BSD_FrobeniusDegreeNonneg_OPEN 2417 := fun r => by
  have hap : (a_p 2417 : ℝ) = -24 := by exact_mod_cast BSD_ap_p2417
  have key : r ^ 2 - (a_p 2417 : ℝ) * r + ((2417 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 9092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=2423: a_p=+75, 4p-a_p²=4067
theorem BSD_DegreeNonneg_p2423 : BSD_FrobeniusDegreeNonneg_OPEN 2423 := fun r => by
  have hap : (a_p 2423 : ℝ) = 75 := by exact_mod_cast BSD_ap_p2423
  have key : r ^ 2 - (a_p 2423 : ℝ) * r + ((2423 : ℕ) : ℝ) =
      (r - 75/2) ^ 2 + 4067/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (75 : ℝ)/2)]

-- p=2437: a_p=+40, 4p-a_p²=8148
theorem BSD_DegreeNonneg_p2437 : BSD_FrobeniusDegreeNonneg_OPEN 2437 := fun r => by
  have hap : (a_p 2437 : ℝ) = 40 := by exact_mod_cast BSD_ap_p2437
  have key : r ^ 2 - (a_p 2437 : ℝ) * r + ((2437 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 8148/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

-- p=2441: a_p=+18, 4p-a_p²=9440
theorem BSD_DegreeNonneg_p2441 : BSD_FrobeniusDegreeNonneg_OPEN 2441 := fun r => by
  have hap : (a_p 2441 : ℝ) = 18 := by exact_mod_cast BSD_ap_p2441
  have key : r ^ 2 - (a_p 2441 : ℝ) * r + ((2441 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 9440/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=2447: a_p=+27, 4p-a_p²=9059
theorem BSD_DegreeNonneg_p2447 : BSD_FrobeniusDegreeNonneg_OPEN 2447 := fun r => by
  have hap : (a_p 2447 : ℝ) = 27 := by exact_mod_cast BSD_ap_p2447
  have key : r ^ 2 - (a_p 2447 : ℝ) * r + ((2447 : ℕ) : ℝ) =
      (r - 27/2) ^ 2 + 9059/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (27 : ℝ)/2)]

-- p=2459: a_p=+92, 4p-a_p²=1372
theorem BSD_DegreeNonneg_p2459 : BSD_FrobeniusDegreeNonneg_OPEN 2459 := fun r => by
  have hap : (a_p 2459 : ℝ) = 92 := by exact_mod_cast BSD_ap_p2459
  have key : r ^ 2 - (a_p 2459 : ℝ) * r + ((2459 : ℕ) : ℝ) =
      (r - 92/2) ^ 2 + 1372/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (92 : ℝ)/2)]

-- p=2467: a_p=+7, 4p-a_p²=9819
theorem BSD_DegreeNonneg_p2467 : BSD_FrobeniusDegreeNonneg_OPEN 2467 := fun r => by
  have hap : (a_p 2467 : ℝ) = 7 := by exact_mod_cast BSD_ap_p2467
  have key : r ^ 2 - (a_p 2467 : ℝ) * r + ((2467 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 9819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

-- p=2473: a_p=+13, 4p-a_p²=9723
theorem BSD_DegreeNonneg_p2473 : BSD_FrobeniusDegreeNonneg_OPEN 2473 := fun r => by
  have hap : (a_p 2473 : ℝ) = 13 := by exact_mod_cast BSD_ap_p2473
  have key : r ^ 2 - (a_p 2473 : ℝ) * r + ((2473 : ℕ) : ℝ) =
      (r - 13/2) ^ 2 + 9723/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (13 : ℝ)/2)]

-- p=2477: a_p=+8, 4p-a_p²=9844
theorem BSD_DegreeNonneg_p2477 : BSD_FrobeniusDegreeNonneg_OPEN 2477 := fun r => by
  have hap : (a_p 2477 : ℝ) = 8 := by exact_mod_cast BSD_ap_p2477
  have key : r ^ 2 - (a_p 2477 : ℝ) * r + ((2477 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 9844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

-- p=2503: a_p=-12, 4p-a_p²=9868
theorem BSD_DegreeNonneg_p2503 : BSD_FrobeniusDegreeNonneg_OPEN 2503 := fun r => by
  have hap : (a_p 2503 : ℝ) = -12 := by exact_mod_cast BSD_ap_p2503
  have key : r ^ 2 - (a_p 2503 : ℝ) * r + ((2503 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 9868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2417 : BSD_Hasse_OPEN 2417 :=
  BSD_hasse_of_degree_nonneg 2417 BSD_DegreeNonneg_p2417
theorem BSD_Hasse_OPEN_p2423 : BSD_Hasse_OPEN 2423 :=
  BSD_hasse_of_degree_nonneg 2423 BSD_DegreeNonneg_p2423
theorem BSD_Hasse_OPEN_p2437 : BSD_Hasse_OPEN 2437 :=
  BSD_hasse_of_degree_nonneg 2437 BSD_DegreeNonneg_p2437
theorem BSD_Hasse_OPEN_p2441 : BSD_Hasse_OPEN 2441 :=
  BSD_hasse_of_degree_nonneg 2441 BSD_DegreeNonneg_p2441
theorem BSD_Hasse_OPEN_p2447 : BSD_Hasse_OPEN 2447 :=
  BSD_hasse_of_degree_nonneg 2447 BSD_DegreeNonneg_p2447
theorem BSD_Hasse_OPEN_p2459 : BSD_Hasse_OPEN 2459 :=
  BSD_hasse_of_degree_nonneg 2459 BSD_DegreeNonneg_p2459
theorem BSD_Hasse_OPEN_p2467 : BSD_Hasse_OPEN 2467 :=
  BSD_hasse_of_degree_nonneg 2467 BSD_DegreeNonneg_p2467
theorem BSD_Hasse_OPEN_p2473 : BSD_Hasse_OPEN 2473 :=
  BSD_hasse_of_degree_nonneg 2473 BSD_DegreeNonneg_p2473
theorem BSD_Hasse_OPEN_p2477 : BSD_Hasse_OPEN 2477 :=
  BSD_hasse_of_degree_nonneg 2477 BSD_DegreeNonneg_p2477
theorem BSD_Hasse_OPEN_p2503 : BSD_Hasse_OPEN 2503 :=
  BSD_hasse_of_degree_nonneg 2503 BSD_DegreeNonneg_p2503

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2417 : (a_p 2417 : ℝ) ^ 2 ≤ 4 * (2417 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2417
theorem BSD_HasseBound_Disc_p2423 : (a_p 2423 : ℝ) ^ 2 ≤ 4 * (2423 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2423
theorem BSD_HasseBound_Disc_p2437 : (a_p 2437 : ℝ) ^ 2 ≤ 4 * (2437 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2437
theorem BSD_HasseBound_Disc_p2441 : (a_p 2441 : ℝ) ^ 2 ≤ 4 * (2441 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2441
theorem BSD_HasseBound_Disc_p2447 : (a_p 2447 : ℝ) ^ 2 ≤ 4 * (2447 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2447
theorem BSD_HasseBound_Disc_p2459 : (a_p 2459 : ℝ) ^ 2 ≤ 4 * (2459 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2459
theorem BSD_HasseBound_Disc_p2467 : (a_p 2467 : ℝ) ^ 2 ≤ 4 * (2467 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2467
theorem BSD_HasseBound_Disc_p2473 : (a_p 2473 : ℝ) ^ 2 ≤ 4 * (2473 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2473
theorem BSD_HasseBound_Disc_p2477 : (a_p 2477 : ℝ) ^ 2 ≤ 4 * (2477 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2477
theorem BSD_HasseBound_Disc_p2503 : (a_p 2503 : ℝ) ^ 2 ≤ 4 * (2503 : ℝ) :=
  BSD_disc_from_deg_802 BSD_DegreeNonneg_p2503

end Towers.BSD