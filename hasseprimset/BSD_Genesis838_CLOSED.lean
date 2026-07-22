/-
================================================================
Towers / BSD / BSD_Genesis838_CLOSED  (genesis-838)

HasseBridge Tier C: Hasse bounds for primes
5441..5507 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5441: card=5390, a_p=+52, disc=-19060
  p=5443: card=5351, a_p=+93, disc=-13123
  p=5449: card=5325, a_p=+125, disc=-6171
  p=5471: card=5597, a_p=-125, disc=-6259
  p=5477: card=5594, a_p=-116, disc=-8452
  p=5479: card=5605, a_p=-125, disc=-6291
  p=5483: card=5520, a_p=-36, disc=-20636
  p=5501: card=5609, a_p=-107, disc=-10555
  p=5503: card=5389, a_p=+115, disc=-8787
  p=5507: card=5540, a_p=-32, disc=-21004

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_838 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i838_p5441 : Fact (5441 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5443 : Fact (5443 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5449 : Fact (5449 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5471 : Fact (5471 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5477 : Fact (5477 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5479 : Fact (5479 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5483 : Fact (5483 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5501 : Fact (5501 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5503 : Fact (5503 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5507 : Fact (5507 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5441 : (E143_Finset 5441).card = 5390 := by native_decide
theorem BSD_E143_card_p5443 : (E143_Finset 5443).card = 5351 := by native_decide
theorem BSD_E143_card_p5449 : (E143_Finset 5449).card = 5325 := by native_decide
theorem BSD_E143_card_p5471 : (E143_Finset 5471).card = 5597 := by native_decide
theorem BSD_E143_card_p5477 : (E143_Finset 5477).card = 5594 := by native_decide
theorem BSD_E143_card_p5479 : (E143_Finset 5479).card = 5605 := by native_decide
theorem BSD_E143_card_p5483 : (E143_Finset 5483).card = 5520 := by native_decide
theorem BSD_E143_card_p5501 : (E143_Finset 5501).card = 5609 := by native_decide
theorem BSD_E143_card_p5503 : (E143_Finset 5503).card = 5389 := by native_decide
theorem BSD_E143_card_p5507 : (E143_Finset 5507).card = 5540 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5441 : a_p 5441 = (52 : ℤ) := by
  have h := BSD_E143_card_p5441; unfold a_p; omega
theorem BSD_ap_p5443 : a_p 5443 = (93 : ℤ) := by
  have h := BSD_E143_card_p5443; unfold a_p; omega
theorem BSD_ap_p5449 : a_p 5449 = (125 : ℤ) := by
  have h := BSD_E143_card_p5449; unfold a_p; omega
theorem BSD_ap_p5471 : a_p 5471 = (-125 : ℤ) := by
  have h := BSD_E143_card_p5471; unfold a_p; omega
theorem BSD_ap_p5477 : a_p 5477 = (-116 : ℤ) := by
  have h := BSD_E143_card_p5477; unfold a_p; omega
theorem BSD_ap_p5479 : a_p 5479 = (-125 : ℤ) := by
  have h := BSD_E143_card_p5479; unfold a_p; omega
theorem BSD_ap_p5483 : a_p 5483 = (-36 : ℤ) := by
  have h := BSD_E143_card_p5483; unfold a_p; omega
theorem BSD_ap_p5501 : a_p 5501 = (-107 : ℤ) := by
  have h := BSD_E143_card_p5501; unfold a_p; omega
theorem BSD_ap_p5503 : a_p 5503 = (115 : ℤ) := by
  have h := BSD_E143_card_p5503; unfold a_p; omega
theorem BSD_ap_p5507 : a_p 5507 = (-32 : ℤ) := by
  have h := BSD_E143_card_p5507; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5441: a_p=+52, 4p-a_p²=19060
theorem BSD_DegreeNonneg_p5441 : BSD_FrobeniusDegreeNonneg_OPEN 5441 := fun r => by
  have hap : (a_p 5441 : ℝ) = 52 := by exact_mod_cast BSD_ap_p5441
  have key : r ^ 2 - (a_p 5441 : ℝ) * r + ((5441 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 19060/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

-- p=5443: a_p=+93, 4p-a_p²=13123
theorem BSD_DegreeNonneg_p5443 : BSD_FrobeniusDegreeNonneg_OPEN 5443 := fun r => by
  have hap : (a_p 5443 : ℝ) = 93 := by exact_mod_cast BSD_ap_p5443
  have key : r ^ 2 - (a_p 5443 : ℝ) * r + ((5443 : ℕ) : ℝ) =
      (r - 93/2) ^ 2 + 13123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (93 : ℝ)/2)]

-- p=5449: a_p=+125, 4p-a_p²=6171
theorem BSD_DegreeNonneg_p5449 : BSD_FrobeniusDegreeNonneg_OPEN 5449 := fun r => by
  have hap : (a_p 5449 : ℝ) = 125 := by exact_mod_cast BSD_ap_p5449
  have key : r ^ 2 - (a_p 5449 : ℝ) * r + ((5449 : ℕ) : ℝ) =
      (r - 125/2) ^ 2 + 6171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (125 : ℝ)/2)]

-- p=5471: a_p=-125, 4p-a_p²=6259
theorem BSD_DegreeNonneg_p5471 : BSD_FrobeniusDegreeNonneg_OPEN 5471 := fun r => by
  have hap : (a_p 5471 : ℝ) = -125 := by exact_mod_cast BSD_ap_p5471
  have key : r ^ 2 - (a_p 5471 : ℝ) * r + ((5471 : ℕ) : ℝ) =
      (r + 125/2) ^ 2 + 6259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (125 : ℝ)/2)]

-- p=5477: a_p=-116, 4p-a_p²=8452
theorem BSD_DegreeNonneg_p5477 : BSD_FrobeniusDegreeNonneg_OPEN 5477 := fun r => by
  have hap : (a_p 5477 : ℝ) = -116 := by exact_mod_cast BSD_ap_p5477
  have key : r ^ 2 - (a_p 5477 : ℝ) * r + ((5477 : ℕ) : ℝ) =
      (r + 116/2) ^ 2 + 8452/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (116 : ℝ)/2)]

-- p=5479: a_p=-125, 4p-a_p²=6291
theorem BSD_DegreeNonneg_p5479 : BSD_FrobeniusDegreeNonneg_OPEN 5479 := fun r => by
  have hap : (a_p 5479 : ℝ) = -125 := by exact_mod_cast BSD_ap_p5479
  have key : r ^ 2 - (a_p 5479 : ℝ) * r + ((5479 : ℕ) : ℝ) =
      (r + 125/2) ^ 2 + 6291/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (125 : ℝ)/2)]

-- p=5483: a_p=-36, 4p-a_p²=20636
theorem BSD_DegreeNonneg_p5483 : BSD_FrobeniusDegreeNonneg_OPEN 5483 := fun r => by
  have hap : (a_p 5483 : ℝ) = -36 := by exact_mod_cast BSD_ap_p5483
  have key : r ^ 2 - (a_p 5483 : ℝ) * r + ((5483 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 20636/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

-- p=5501: a_p=-107, 4p-a_p²=10555
theorem BSD_DegreeNonneg_p5501 : BSD_FrobeniusDegreeNonneg_OPEN 5501 := fun r => by
  have hap : (a_p 5501 : ℝ) = -107 := by exact_mod_cast BSD_ap_p5501
  have key : r ^ 2 - (a_p 5501 : ℝ) * r + ((5501 : ℕ) : ℝ) =
      (r + 107/2) ^ 2 + 10555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (107 : ℝ)/2)]

-- p=5503: a_p=+115, 4p-a_p²=8787
theorem BSD_DegreeNonneg_p5503 : BSD_FrobeniusDegreeNonneg_OPEN 5503 := fun r => by
  have hap : (a_p 5503 : ℝ) = 115 := by exact_mod_cast BSD_ap_p5503
  have key : r ^ 2 - (a_p 5503 : ℝ) * r + ((5503 : ℕ) : ℝ) =
      (r - 115/2) ^ 2 + 8787/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (115 : ℝ)/2)]

-- p=5507: a_p=-32, 4p-a_p²=21004
theorem BSD_DegreeNonneg_p5507 : BSD_FrobeniusDegreeNonneg_OPEN 5507 := fun r => by
  have hap : (a_p 5507 : ℝ) = -32 := by exact_mod_cast BSD_ap_p5507
  have key : r ^ 2 - (a_p 5507 : ℝ) * r + ((5507 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 21004/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5441 : BSD_Hasse_OPEN 5441 :=
  BSD_hasse_of_degree_nonneg 5441 BSD_DegreeNonneg_p5441
theorem BSD_Hasse_OPEN_p5443 : BSD_Hasse_OPEN 5443 :=
  BSD_hasse_of_degree_nonneg 5443 BSD_DegreeNonneg_p5443
theorem BSD_Hasse_OPEN_p5449 : BSD_Hasse_OPEN 5449 :=
  BSD_hasse_of_degree_nonneg 5449 BSD_DegreeNonneg_p5449
theorem BSD_Hasse_OPEN_p5471 : BSD_Hasse_OPEN 5471 :=
  BSD_hasse_of_degree_nonneg 5471 BSD_DegreeNonneg_p5471
theorem BSD_Hasse_OPEN_p5477 : BSD_Hasse_OPEN 5477 :=
  BSD_hasse_of_degree_nonneg 5477 BSD_DegreeNonneg_p5477
theorem BSD_Hasse_OPEN_p5479 : BSD_Hasse_OPEN 5479 :=
  BSD_hasse_of_degree_nonneg 5479 BSD_DegreeNonneg_p5479
theorem BSD_Hasse_OPEN_p5483 : BSD_Hasse_OPEN 5483 :=
  BSD_hasse_of_degree_nonneg 5483 BSD_DegreeNonneg_p5483
theorem BSD_Hasse_OPEN_p5501 : BSD_Hasse_OPEN 5501 :=
  BSD_hasse_of_degree_nonneg 5501 BSD_DegreeNonneg_p5501
theorem BSD_Hasse_OPEN_p5503 : BSD_Hasse_OPEN 5503 :=
  BSD_hasse_of_degree_nonneg 5503 BSD_DegreeNonneg_p5503
theorem BSD_Hasse_OPEN_p5507 : BSD_Hasse_OPEN 5507 :=
  BSD_hasse_of_degree_nonneg 5507 BSD_DegreeNonneg_p5507

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5441 : (a_p 5441 : ℝ) ^ 2 ≤ 4 * (5441 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5441
theorem BSD_HasseBound_Disc_p5443 : (a_p 5443 : ℝ) ^ 2 ≤ 4 * (5443 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5443
theorem BSD_HasseBound_Disc_p5449 : (a_p 5449 : ℝ) ^ 2 ≤ 4 * (5449 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5449
theorem BSD_HasseBound_Disc_p5471 : (a_p 5471 : ℝ) ^ 2 ≤ 4 * (5471 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5471
theorem BSD_HasseBound_Disc_p5477 : (a_p 5477 : ℝ) ^ 2 ≤ 4 * (5477 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5477
theorem BSD_HasseBound_Disc_p5479 : (a_p 5479 : ℝ) ^ 2 ≤ 4 * (5479 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5479
theorem BSD_HasseBound_Disc_p5483 : (a_p 5483 : ℝ) ^ 2 ≤ 4 * (5483 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5483
theorem BSD_HasseBound_Disc_p5501 : (a_p 5501 : ℝ) ^ 2 ≤ 4 * (5501 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5501
theorem BSD_HasseBound_Disc_p5503 : (a_p 5503 : ℝ) ^ 2 ≤ 4 * (5503 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5503
theorem BSD_HasseBound_Disc_p5507 : (a_p 5507 : ℝ) ^ 2 ≤ 4 * (5507 : ℝ) :=
  BSD_disc_from_deg_838 BSD_DegreeNonneg_p5507

end Towers.BSD